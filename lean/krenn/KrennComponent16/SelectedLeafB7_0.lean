import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "689831d649dd6712d73214de03d6fb36546c9232128af9c40b669a8dd9acab0c"
def certificateSHA256 : String := "cbbe77a067a616bfde999ec8192fbd8951e4fbd5be27e8b11dce5e1374d903b9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 668 := ![
  0,
  1,
  2,
  3,
  4,
  6,
  13,
  23,
  166,
  167,
  302,
  314,
  316,
  318,
  366,
  408,
  428,
  434,
  440,
  448,
  478,
  498,
  528,
  571,
  584,
  612,
  661,
  662,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (31, 1), (47, 1), (63, 1)] }, { coefficient := 2, powers := [(6, 1), (13, 1), (31, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (26, 1), (31, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (45, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (25, 1), (45, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (25, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (30, 1), (34, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (30, 1), (34, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (27, 1), (30, 1), (34, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (30, 1), (34, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (47, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (27, 1), (34, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (47, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (26, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (25, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (31, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (25, 1), (45, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(6, 1), (13, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (47, 1), (54, 1)] }, { coefficient := -2, powers := [(13, 1), (26, 1), (31, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (26, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (19, 1), (27, 1), (34, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (27, 1), (29, 1), (34, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (21, 1), (27, 1), (30, 1), (34, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (26, 1), (27, 1), (30, 1), (34, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (27, 1), (29, 1), (34, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (31, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB7_0.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB7_0
