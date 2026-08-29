import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB0_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "47977d6daaaf339fdb4df13f9c031f729332422700d6db04bc7e6c5ada8c7951"
def certificateSHA256 : String := "f2065b7b225a6d685768db62cfc08a67feded25a8ff070f90af2b2be8671c46b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 668 := ![
  12,
  13,
  23,
  32,
  175,
  176,
  302,
  316,
  440,
  442,
  448,
  479,
  481,
  503,
  585,
  590,
  649,
  650,
  661,
  662,
  664,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(9, 1), (24, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (40, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (40, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (25, 1), (27, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (27, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (27, 1), (32, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (27, 1), (32, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (32, 1), (40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (19, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (32, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (32, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (32, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (32, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (9, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (20, 1), (25, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (32, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (37, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (37, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (25, 1), (32, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (32, 1), (38, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (32, 1), (38, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (29, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (32, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (31, 1), (32, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (32, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (32, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (38, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (38, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (50, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (50, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (13, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (40, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (40, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (25, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (32, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (32, 1), (40, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (9, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (39, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (9, 1), (37, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (47, 2), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (32, 1), (37, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (20, 1), (25, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (32, 1), (47, 2), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (25, 1), (32, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1), (53, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (29, 1), (48, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (37, 1), (38, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (21, 1), (32, 1), (37, 1), (39, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (47, 1), (48, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (48, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (47, 2), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (37, 1), (38, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (38, 1), (47, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (39, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (47, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (32, 1), (39, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (32, 1), (38, 1), (47, 2), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (32, 1), (38, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (40, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (38, 1), (40, 1), (60, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (39, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (40, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (40, 1), (53, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (32, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (21, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (9, 1), (58, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (47, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (32, 1), (53, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (32, 1), (39, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (9, 1), (37, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (32, 1), (37, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (32, 1), (37, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (31, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (31, 1), (32, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (32, 1), (38, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (32, 1), (38, 1), (53, 1), (62, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB0_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB0_4
