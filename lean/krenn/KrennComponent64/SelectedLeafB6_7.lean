import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component64.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0f2a29ec8a01ecd3ae4ed5c8b5ed0af932f10532f0830cdfbfcde1242e33d352"
def certificateSHA256 : String := "de07935bb2f0300f7b9ae4cc44bafb70e37290b41ab35246e27e4202825f6917"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 641 := ![
  7,
  9,
  10,
  16,
  24,
  26,
  27,
  29,
  30,
  32,
  161,
  163,
  166,
  168,
  170,
  172,
  222,
  231,
  235,
  243,
  349,
  350,
  351,
  352,
  363,
  367,
  372,
  388,
  415,
  416,
  418,
  466,
  548,
  570,
  576,
  632,
  634,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (34, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (27, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (49, 1), (56, 1)] }, { coefficient := -2, powers := [(9, 1), (23, 1), (34, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (30, 1), (34, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 2, powers := [(23, 1), (34, 1), (47, 1), (53, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1), (46, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (34, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (34, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(3, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (30, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (33, 1), (39, 1), (42, 1)] }, { coefficient := 2, powers := [(6, 1), (23, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (34, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (23, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (34, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 2), (28, 1), (33, 1), (40, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (33, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (31, 1), (33, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (33, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (33, 1), (34, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (28, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (28, 1), (40, 1), (52, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (31, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (47, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (34, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (14, 1), (34, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (14, 1), (20, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (34, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (28, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (20, 1), (45, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (28, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (34, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (34, 1), (45, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (30, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (13, 1), (23, 1), (34, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (30, 1), (34, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (33, 1), (34, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (34, 1), (47, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (34, 1), (46, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (47, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (41, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (28, 1), (40, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (31, 1), (34, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (47, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (34, 1), (47, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 2), (28, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (40, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (9, 1), (20, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (45, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (39, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (39, 1), (44, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (27, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (27, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (20, 1), (27, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (27, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (28, 1), (33, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (33, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (31, 1), (33, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (33, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (6, 1), (23, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 2), (23, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (23, 1), (31, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (31, 1), (34, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (28, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (28, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(5, 1), (9, 1), (20, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (47, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (34, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (34, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (9, 1), (20, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (20, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (31, 1), (34, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (34, 1), (47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 2), (28, 1), (40, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (20, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (31, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (47, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (40, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (20, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (23, 1), (28, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 2), (23, 1), (28, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (23, 1), (31, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (47, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (31, 1), (34, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (23, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(40, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (34, 1), (59, 1)] }, { coefficient := 2, powers := [(6, 1), (20, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (23, 1), (34, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (30, 1), (34, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (34, 1)] }, { coefficient := -2, powers := [(23, 1), (34, 1), (47, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(30, 1), (34, 1), (46, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (34, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (20, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (31, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (20, 1), (39, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (28, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (40, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 2), (28, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (40, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (6, 1), (28, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (28, 1), (46, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(3, 1), (9, 1), (20, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (45, 1), (47, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (28, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 2), (28, 1), (40, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 2), (28, 1), (40, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (45, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (46, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (31, 1), (34, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (31, 1), (34, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (45, 1), (47, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (46, 1), (47, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (28, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (34, 1), (45, 1), (47, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (34, 1), (46, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (38, 1), (39, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (46, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (31, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (39, 1), (47, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (47, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (47, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (39, 1), (47, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (20, 1), (33, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (33, 1), (39, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (20, 1), (27, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (27, 1), (39, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (37, 1)] }, { coefficient := -2, powers := [(8, 1), (9, 1), (23, 1), (31, 1), (34, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (30, 1), (31, 1), (34, 1), (46, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (31, 1), (34, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (31, 1), (34, 1), (46, 1), (47, 1)] }, { coefficient := -1, powers := [(9, 1), (24, 1), (40, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (47, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component64.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component64.SelectedLeafB6_7
