import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5631440fc332b32dd1923ae54b16a6b7ac112bcf53fed062bf42acde804b1a16"
def certificateSHA256 : String := "419340001e2a4c8e35b45aa7c97b56dd01ee4e5e6b68503662452d3773dc4a04"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 668 := ![
  0,
  1,
  2,
  3,
  13,
  23,
  24,
  30,
  37,
  162,
  247,
  302,
  314,
  316,
  328,
  407,
  408,
  440,
  448,
  458,
  478,
  584,
  585,
  610,
  654,
  661,
  662,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (27, 1), (37, 1), (38, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (38, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (34, 1), (48, 1), (63, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (48, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (37, 1), (38, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (37, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (13, 1), (31, 1), (37, 1), (53, 1), (62, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (42, 1), (43, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (24, 1), (43, 1), (47, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (29, 1), (42, 1), (43, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (29, 1), (43, 1), (47, 1), (58, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (31, 1), (37, 1), (42, 1), (64, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (31, 1), (37, 1), (47, 1), (64, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (29, 1), (31, 1), (37, 1), (42, 1), (64, 2), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (19, 1), (29, 1), (31, 1), (37, 1), (47, 1), (64, 2), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (42, 1), (62, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (47, 1), (62, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (53, 1), (62, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (57, 1), (62, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (34, 1), (53, 2), (64, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (37, 1), (40, 1), (42, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (37, 1), (40, 1), (47, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (37, 1), (40, 1), (42, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (29, 1), (37, 1), (40, 1), (47, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1), (53, 2), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (43, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (34, 1), (58, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (58, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (54, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (34, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (34, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (29, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (24, 1), (31, 1), (37, 1), (64, 2)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (29, 1), (31, 1), (37, 1), (64, 2)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (37, 1), (40, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (37, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (34, 1), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (38, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (64, 2)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (26, 1), (31, 1), (37, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (21, 1), (31, 1), (37, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (38, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (34, 1), (48, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (37, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (37, 1), (38, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (37, 1), (38, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (31, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (34, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (34, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (13, 1), (26, 1), (31, 1), (37, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (26, 1), (42, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (24, 1), (26, 1), (43, 1), (47, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (29, 1), (42, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (29, 1), (43, 1), (47, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (26, 1), (31, 1), (37, 1), (42, 1), (64, 2)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (24, 1), (26, 1), (31, 1), (37, 1), (47, 1), (64, 2)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (26, 1), (29, 1), (31, 1), (37, 1), (42, 1), (64, 2)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (19, 1), (26, 1), (29, 1), (31, 1), (37, 1), (47, 1), (64, 2)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (21, 1), (26, 1), (31, 1), (37, 1), (42, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (21, 1), (26, 1), (31, 1), (37, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (21, 1), (26, 1), (31, 1), (37, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (21, 1), (26, 1), (31, 1), (37, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (30, 1), (34, 1), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (31, 1), (34, 1), (53, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (34, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (26, 1), (37, 1), (40, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (26, 1), (37, 1), (40, 1), (47, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (29, 1), (37, 1), (40, 1), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (29, 1), (37, 1), (40, 1), (47, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 2), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (43, 1), (54, 1), (65, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB7_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB7_3
