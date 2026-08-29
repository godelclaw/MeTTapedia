import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cd938e101eba2a8374b9e4da318a4877be1a9137637a86e45d279e032753ecf8"
def certificateSHA256 : String := "9920459c78e69c97b09951812014f22f744fcb4179b5465e95a46fb61cce1a8b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 668 := ![
  0,
  1,
  2,
  3,
  4,
  7,
  9,
  12,
  13,
  23,
  32,
  113,
  144,
  145,
  162,
  298,
  301,
  302,
  315,
  316,
  366,
  440,
  442,
  448,
  462,
  503,
  558,
  571,
  584,
  585,
  595,
  619,
  661,
  662,
  663,
  664,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (30, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (21, 1), (30, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (29, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (29, 1), (58, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (30, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (31, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (31, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (31, 1), (53, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (31, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (17, 1), (28, 1), (34, 1), (63, 2)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (45, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (25, 1), (45, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (33, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (47, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (25, 1), (42, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(21, 1), (25, 1), (47, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (17, 1), (27, 1), (33, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (25, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (53, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (31, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (21, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (53, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (28, 1), (34, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (25, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (34, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (25, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (30, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (17, 1), (28, 1), (34, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (21, 1), (30, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (29, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (45, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (37, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (25, 1), (45, 1), (54, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1), (21, 1), (29, 1), (49, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (21, 1), (30, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (31, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(13, 1), (21, 1), (31, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (40, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (40, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (31, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_2
