import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b0e7a8c1d7952a6c8bafa90beccd52a53700c5912aa3343babddcf464f913c31"
def certificateSHA256 : String := "de55dc2322dcc5645ec491943a55406f4066977679173d2dc5b258e08ad187c8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 671 := ![
  15,
  19,
  24,
  26,
  29,
  278,
  309,
  310,
  317,
  412,
  420,
  421,
  423,
  439,
  447,
  540,
  581,
  582,
  607,
  611,
  661,
  664,
  666,
  667,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (35, 1), (47, 1), (51, 1)] }, { coefficient := 2, powers := [(0, 1), (31, 1), (35, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (35, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (40, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 2, powers := [(6, 1), (19, 1), (31, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (34, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (35, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (35, 1), (45, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (45, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (45, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (51, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (52, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (51, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (52, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (35, 1), (53, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (51, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (53, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (35, 1), (46, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (46, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (19, 1), (46, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (35, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (35, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (35, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (23, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (23, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (40, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (54, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (47, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (47, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (47, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 2), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 2), (63, 1)] }, { coefficient := 1, powers := [(20, 2), (44, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(46, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 2), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(44, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(46, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (23, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (51, 2), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (56, 2), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(46, 1), (52, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (19, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (49, 1), (56, 2), (63, 1)] }, { coefficient := -1, powers := [(20, 2), (44, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(20, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(51, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (37, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (37, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (40, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (47, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (35, 1), (47, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (37, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (37, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (40, 1), (51, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (40, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (47, 1), (54, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (35, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (35, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (28, 1), (35, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (28, 1), (35, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (24, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(3, 1), (18, 1), (23, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (24, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (19, 1), (23, 1), (24, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (18, 1), (19, 1), (23, 1), (24, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (24, 1), (28, 1), (40, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (19, 1), (24, 1), (28, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (51, 2), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (51, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (49, 1), (56, 2), (63, 1)] }, { coefficient := 1, powers := [(20, 2), (24, 1), (44, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (44, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (46, 1), (49, 1), (52, 1), (63, 2)] }, { coefficient := -1, powers := [(20, 1), (24, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (51, 2)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 2)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (56, 2)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (31, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (19, 1), (31, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (19, 1), (23, 1), (56, 1), (59, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_1_6.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_1_6
