import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1a6fa784b11d35add296fd7460064c045bb129a6f9da057b03426817fc7ea7c0"
def certificateSHA256 : String := "edbaedce34a256e9bdf28cebe4556ac88003febb96b4aa3dd08e0761182978ab"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 46 → Fin 667 := ![
  0,
  10,
  19,
  142,
  162,
  163,
  164,
  166,
  167,
  246,
  279,
  294,
  295,
  301,
  315,
  317,
  318,
  323,
  327,
  345,
  351,
  355,
  403,
  409,
  429,
  431,
  432,
  435,
  437,
  438,
  440,
  443,
  449,
  466,
  491,
  496,
  580,
  581,
  584,
  645,
  649,
  657,
  658,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 46 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }, { coefficient := -1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 46 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (45, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (30, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (29, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (25, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (24, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (30, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (29, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(23, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (46, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (46, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (37, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (30, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (37, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (25, 1), (45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (45, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (45, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (30, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (29, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (30, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (45, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (37, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (23, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (25, 1), (37, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (20, 1), (29, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (24, 1), (25, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (25, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (25, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (29, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }]
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
    ¬ ∀ index : Fin 46,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_2_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_2_0
