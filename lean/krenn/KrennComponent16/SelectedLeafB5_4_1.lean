import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cc79db571d05382dc60115773fd5ce5c15d928b0f642980a8d6779c8193168fe"
def certificateSHA256 : String := "0419151241ac0d3784b739ad411f7fb6823fb9867dd4562ba7ae4f374cfd4f50"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 671 := ![
  4,
  13,
  23,
  166,
  167,
  247,
  298,
  302,
  314,
  316,
  321,
  407,
  408,
  430,
  433,
  438,
  440,
  448,
  454,
  455,
  462,
  478,
  503,
  584,
  585,
  610,
  649,
  653,
  661,
  662,
  664,
  666,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (27, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (45, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(3, 1), (25, 1), (48, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (37, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (19, 1), (25, 1), (55, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (21, 1), (25, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (20, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (47, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(27, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (25, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (45, 1), (47, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [(45, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (19, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (21, 1), (26, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (47, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (45, 1), (47, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(27, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := 2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (26, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (26, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (26, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (26, 1), (47, 1), (53, 2)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (26, 1), (53, 2)] }, { coefficient := 2, powers := [(0, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (53, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (25, 1), (45, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (26, 1), (39, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (26, 1), (47, 1), (53, 2)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (53, 2)] }, { coefficient := -2, powers := [(0, 1), (38, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 2), (21, 1), (26, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (21, 1), (26, 1), (53, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (21, 1), (25, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (20, 1), (25, 1), (26, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (27, 1), (45, 1), (47, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -2, powers := [(3, 1), (13, 1), (21, 1), (31, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(21, 1), (27, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -2, powers := [(21, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (21, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(21, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_4_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_4_1
