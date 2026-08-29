import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_0_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b581a0d6cb301d02afd172aa982967a5c3f5bcd20cdbb3fc74168b45520dd1cf"
def certificateSHA256 : String := "f7b1b8b043c2614b934cee0d6a6041b1f8af1cfaaa5248868be4027241954ecf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 671 := ![
  4,
  6,
  12,
  23,
  142,
  170,
  171,
  247,
  302,
  316,
  366,
  435,
  440,
  455,
  503,
  584,
  585,
  610,
  620,
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
def selectedEquations : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (31, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (38, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (25, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (25, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (45, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (45, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (38, 1), (45, 1), (60, 2)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (37, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (19, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(38, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (21, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (60, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (60, 2)] }, { coefficient := -1, powers := [(5, 1), (38, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(21, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (62, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (61, 1)] }, { coefficient := -1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (47, 1)] }, { coefficient := -1, powers := [(26, 1), (53, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (26, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (26, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (26, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (29, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (38, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (21, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (21, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (37, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (21, 1), (37, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (37, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(3, 2), (5, 1), (34, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (6, 1), (34, 1), (60, 2)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (34, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (34, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (34, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (38, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_0_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_0_4
