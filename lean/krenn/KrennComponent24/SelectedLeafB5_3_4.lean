import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB5_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f6e29fc146946fa455537e06833a5a1b37d52cd3a05b836b0422c6b8218738b5"
def certificateSHA256 : String := "4a47c69df98271dcf3c8452be8650d4f1747ac537acb9ad375ee4992660ba238"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 673 := ![
  8,
  9,
  14,
  16,
  151,
  172,
  305,
  306,
  308,
  453,
  503,
  589,
  590,
  596,
  606,
  607,
  616,
  653,
  661,
  666,
  667,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (29, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (26, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (29, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1), (38, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (29, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (29, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (29, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (29, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (29, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(29, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (24, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (24, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (29, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (24, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (24, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (24, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (24, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (29, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (26, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (29, 1), (59, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (32, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (20, 1), (29, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (24, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (29, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (30, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (29, 1), (35, 1), (38, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (38, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (32, 1), (38, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (50, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (18, 1), (20, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (20, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (44, 1)] }, { coefficient := 1, powers := [(3, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (42, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (42, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(9, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (42, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (20, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (26, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (35, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (15, 1), (26, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (20, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1)] }, { coefficient := -1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (38, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (35, 1), (38, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (32, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (24, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (29, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (24, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (20, 1), (29, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (24, 1), (26, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (26, 1), (29, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (18, 1), (20, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (20, 1), (29, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (29, 1), (35, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (20, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (35, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (20, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (32, 1), (44, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (35, 1), (38, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 2), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (26, 1), (44, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (35, 1), (38, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB5_3_4.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB5_3_4
