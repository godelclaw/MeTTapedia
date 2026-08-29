import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a0253adfee821326d24d266e05d71a2a247497893b4a8d3c1a4ef093a0bcabe"
def certificateSHA256 : String := "8b2812552505a2e20fd05a1032ee25382a1b62276e9477f55fcbdf8c691ab142"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 640 := ![
  6,
  9,
  13,
  16,
  20,
  23,
  132,
  138,
  167,
  179,
  183,
  194,
  195,
  198,
  282,
  309,
  342,
  343,
  345,
  348,
  349,
  350,
  351,
  360,
  406,
  456,
  460,
  464,
  465,
  470,
  474,
  524,
  555,
  581,
  633,
  634,
  636,
  637,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (35, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (31, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1), (39, 2), (55, 1)] }, { coefficient := -2, powers := [(17, 1), (22, 1), (39, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 2), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (46, 1)] }, { coefficient := -3, powers := [(28, 1), (44, 1), (46, 1)] }, { coefficient := 2, powers := [(28, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (28, 1), (39, 1)] }, { coefficient := -4, powers := [(18, 1), (28, 1), (44, 1)] }, { coefficient := 2, powers := [(18, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (23, 1), (39, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (23, 1), (44, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (39, 1), (52, 1)] }, { coefficient := -2, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(22, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (24, 1), (39, 1)] }, { coefficient := -2, powers := [(22, 1), (24, 1), (44, 1)] }, { coefficient := -2, powers := [(22, 1), (24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (39, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (18, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (23, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (39, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (44, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (51, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (18, 1), (28, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (18, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (23, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (22, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (23, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(22, 1), (23, 1), (44, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(22, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (39, 1)] }, { coefficient := 4, powers := [(12, 1), (28, 1), (44, 1)] }, { coefficient := -2, powers := [(12, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (39, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (44, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (46, 1)] }, { coefficient := -1, powers := [(23, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (39, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (22, 1), (44, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (39, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (17, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (44, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (39, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (39, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (28, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(12, 1), (28, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (39, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (44, 1), (45, 1), (48, 1), (55, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (39, 1), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (22, 1), (23, 1), (44, 1), (52, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(6, 1), (12, 1), (22, 1), (42, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (42, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (16, 1), (28, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (28, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 2), (16, 1), (28, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (16, 1), (28, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (34, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (28, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (28, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (34, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (16, 1), (28, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_6.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_6
