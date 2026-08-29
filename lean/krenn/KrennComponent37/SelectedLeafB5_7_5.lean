import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c5821c9a5bd14a49da60974d62912a3e16c9c0ff4dbe33f6e4bf0674160c1904"
def certificateSHA256 : String := "45e66da3b968711701d791a95a5cc600ec285d2fba19c1083dd1bb967b6d7a9f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 667 := ![
  16,
  23,
  27,
  154,
  182,
  234,
  283,
  298,
  299,
  385,
  430,
  453,
  455,
  487,
  549,
  590,
  604,
  605,
  648,
  656,
  659,
  660,
  661,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (32, 1), (38, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (28, 1), (32, 1), (37, 1), (52, 2), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (32, 1), (38, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (29, 1), (32, 1), (37, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (48, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (66, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (48, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (37, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1), (32, 1), (37, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (32, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(41, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (23, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 2), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (29, 1), (32, 1), (37, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (32, 1), (37, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (28, 1), (32, 1), (37, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (32, 1), (38, 1), (48, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (32, 1), (38, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_7_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_7_5
