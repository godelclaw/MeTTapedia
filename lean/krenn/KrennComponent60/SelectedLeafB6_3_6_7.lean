import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_3_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a99afd50ea7a21a629beb1abbaa627425039dd84812cadc27e44466346dfd4fb"
def certificateSHA256 : String := "4737e8c5209e4c984bd8a9142fd3a8638894efbdb25d14e21b9f27ceafac7317"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 668 := ![
  13,
  24,
  151,
  194,
  298,
  303,
  579,
  582,
  600,
  601,
  653,
  657,
  659,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(20, 1), (22, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (49, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (49, 1), (69, 1)] }, { coefficient := -1, powers := [(30, 1), (36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (42, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (42, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (36, 1), (56, 1), (59, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (59, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (55, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (69, 1)] }, { coefficient := -1, powers := [(55, 1), (66, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (29, 1), (58, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (30, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (36, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (56, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (29, 1), (36, 1), (42, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (55, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (29, 1), (42, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (29, 1), (36, 1), (56, 1), (59, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(13, 1), (29, 1), (36, 1), (59, 1), (66, 1), (69, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (27, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (55, 1), (56, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (29, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (42, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1)] }, { coefficient := -1, powers := [(29, 1), (33, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(29, 1), (55, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (30, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (20, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (36, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 2), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (36, 1), (56, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (36, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (55, 1), (56, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(9, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (30, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (30, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (42, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_3_6_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_3_6_7
