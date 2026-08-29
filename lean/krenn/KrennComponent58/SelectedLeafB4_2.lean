import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a19441e913468b0851e29a78f90a5db7afa2455187c1d1f10d538e5030ddae06"
def certificateSHA256 : String := "ecc288f804c00d8e607be73b425e6ee5bb44a34ad96714d8a91cc71e4a73b423"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 53 → Fin 619 := ![
  6,
  7,
  10,
  12,
  14,
  15,
  22,
  29,
  30,
  32,
  33,
  38,
  41,
  43,
  192,
  195,
  204,
  220,
  221,
  224,
  241,
  314,
  317,
  333,
  339,
  340,
  342,
  352,
  353,
  412,
  438,
  439,
  448,
  449,
  452,
  466,
  473,
  474,
  507,
  518,
  537,
  562,
  573,
  579,
  580,
  596,
  600,
  611,
  612,
  613,
  614,
  615,
  618
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 53 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 53 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (37, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (37, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (37, 1), (43, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (37, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (33, 1), (37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (22, 1), (24, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (30, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (24, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (24, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (24, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (31, 1), (46, 1), (50, 2)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (24, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (27, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (24, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (31, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (50, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (46, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (31, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (22, 1), (24, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (27, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (22, 1), (50, 2), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (22, 1), (50, 1), (52, 1), (54, 2)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (23, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (23, 1), (52, 1), (54, 2)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (27, 1), (50, 2), (52, 1)] }, { coefficient := 4, powers := [(19, 1), (20, 1), (27, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (27, 1), (52, 1), (54, 2)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (24, 1), (25, 1), (27, 1), (50, 2), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (27, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (27, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (25, 1), (50, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (25, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (25, 1), (27, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (25, 1), (30, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (25, 1), (30, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (25, 1), (33, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (31, 1), (45, 1)] }, { coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (25, 1), (27, 1), (50, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (14, 1), (16, 1), (24, 1), (27, 1), (50, 2), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (22, 1), (24, 1), (50, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (23, 1), (24, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (27, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (30, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (24, 1), (30, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (24, 1), (33, 1), (39, 1), (54, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (24, 1), (27, 1), (50, 2)] }, { coefficient := -3, powers := [(14, 1), (16, 1), (24, 1), (27, 1), (50, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (19, 1), (24, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (22, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (18, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (30, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (18, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (18, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (18, 1), (22, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (18, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (18, 1), (27, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (18, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (33, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (22, 1), (48, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (30, 1), (43, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (30, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (33, 1), (39, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (22, 1), (48, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (23, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (27, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (27, 1), (48, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (33, 1), (36, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (22, 1), (48, 1), (50, 2)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (27, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (30, 1), (36, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (33, 1), (52, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (30, 1), (37, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (19, 1), (24, 1), (27, 1), (50, 2)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (50, 1), (51, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (22, 1), (24, 1), (50, 2), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (22, 1), (24, 1), (50, 1), (52, 1), (54, 2)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (24, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (24, 1), (52, 1), (54, 2)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (27, 1), (50, 2), (52, 1)] }, { coefficient := -4, powers := [(19, 1), (24, 1), (27, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (27, 1), (52, 1), (54, 2)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (24, 1), (27, 1), (50, 2), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (50, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (27, 1), (51, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (30, 1), (43, 1), (51, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (30, 1), (50, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (39, 1), (51, 1), (55, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (25, 1), (27, 1), (42, 1), (50, 1), (52, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (50, 1), (51, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (24, 1), (27, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (19, 1), (22, 1), (25, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (19, 1), (23, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (25, 1), (27, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(11, 1), (19, 1), (25, 1), (27, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (22, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (22, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (22, 1), (50, 2), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (22, 1), (46, 1), (50, 2)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (23, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (27, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (50, 2), (52, 1)] }, { coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (50, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (25, 1), (50, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (18, 1), (24, 1), (25, 1), (27, 1), (50, 1), (52, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (50, 2), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (46, 1), (50, 2), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (46, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (46, 1), (50, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (16, 1), (24, 1), (27, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (24, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (24, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (24, 1), (50, 2)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (22, 1), (24, 1), (25, 1), (50, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (14, 1), (22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (30, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (14, 1), (30, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (14, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (14, 1), (22, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (14, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (14, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (14, 1), (27, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (22, 1), (50, 2)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (23, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (27, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (22, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (23, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (27, 1), (50, 1), (52, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (27, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (16, 1), (24, 1), (27, 1), (50, 2), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (24, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (24, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (27, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (30, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (24, 1), (27, 1), (42, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (22, 1), (24, 1), (50, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (18, 1), (31, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (23, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (24, 1), (25, 1), (27, 1), (42, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (22, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (30, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (22, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (23, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (27, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (22, 1), (50, 2)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (23, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (22, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (30, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (30, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (11, 1), (33, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (50, 2), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (30, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (22, 1), (24, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (24, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (27, 1), (50, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (27, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(14, 1), (16, 1), (24, 1), (27, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(16, 1), (19, 1), (24, 1), (27, 1), (50, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (31, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (31, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 2)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (18, 1), (24, 1), (25, 1), (27, 1), (42, 1), (50, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (54, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }, { coefficient := -1, powers := [(50, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (22, 1), (37, 1), (50, 1), (57, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (30, 1), (37, 1), (43, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (30, 1), (37, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (33, 1), (37, 1), (39, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (11, 1), (33, 1), (36, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (22, 1), (37, 1), (50, 2), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (22, 1), (46, 1), (50, 2), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (37, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (23, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (27, 1), (37, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (46, 1), (50, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (30, 1), (36, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (37, 1), (50, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (40, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (37, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (40, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (37, 1), (50, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (40, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (46, 1), (50, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (37, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (27, 1), (40, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (36, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (37, 1), (50, 2), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (40, 1), (50, 2), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (40, 1), (50, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (46, 1), (50, 2), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (40, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (36, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (30, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (33, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (22, 1), (34, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (23, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (27, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (30, 1), (34, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (30, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (33, 1), (34, 1), (39, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (22, 1), (28, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (28, 1), (30, 1), (43, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (28, 1), (30, 1), (50, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (28, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (22, 1), (34, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (23, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (27, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (27, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (33, 1), (34, 1), (36, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (22, 1), (34, 1), (50, 2)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (23, 1), (34, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (16, 1), (27, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (30, 1), (34, 1), (36, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 53,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB4_2.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB4_2
