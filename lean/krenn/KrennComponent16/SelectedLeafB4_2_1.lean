import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "971b25dd6340459bdb3021aebb38bcbf3895fa50f6e2ec2256863c1e50262c73"
def certificateSHA256 : String := "d2f9b7e6d54a2e678d4cd727f133494e225833723284fabd99d8b7b71cc122b5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 671 := ![
  4,
  13,
  23,
  31,
  32,
  247,
  302,
  316,
  321,
  430,
  440,
  448,
  462,
  468,
  503,
  572,
  585,
  612,
  649,
  661,
  662,
  664,
  667,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (31, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (8, 1), (25, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (25, 1), (27, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (19, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (42, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (19, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (19, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (45, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (45, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (42, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (45, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (5, 1), (48, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (31, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (37, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (25, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (42, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (31, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (31, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (40, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (37, 1), (40, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (31, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (20, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (20, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (20, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (45, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (42, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (25, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (27, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (45, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (27, 1), (45, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 2, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (27, 1), (48, 1), (53, 2), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (53, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (48, 1), (53, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (45, 1), (53, 2), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (45, 1), (53, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(0, 1), (53, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (39, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (42, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (40, 1), (60, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (37, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (3, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (37, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (37, 1), (47, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (8, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (31, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (20, 1), (31, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (20, 1), (31, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (21, 1), (31, 1), (39, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (13, 1), (21, 1), (37, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (25, 1), (42, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (25, 1), (47, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (25, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (31, 1), (42, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (31, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (31, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (47, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (13, 1), (21, 1), (37, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (27, 1), (45, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (27, 1), (45, 1), (53, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (27, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (21, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (47, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (21, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_2_1
