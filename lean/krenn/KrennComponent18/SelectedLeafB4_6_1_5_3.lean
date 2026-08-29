import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_6_1_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ae36f69803ef7d8103a45a420f80f26e95cb742e2720caad6a05fa7729b3571d"
def certificateSHA256 : String := "cf0c4150846ce45118a41f0ca5cd45dd845908b6763c7f7dcf6db862adb59276"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 673 := ![
  0,
  26,
  35,
  145,
  329,
  596,
  607,
  647,
  656,
  658,
  659,
  661,
  665,
  667,
  668,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(15, 1), (36, 1), (42, 1), (51, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (51, 1), (52, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (36, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(15, 1), (36, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (46, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (33, 1), (46, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (62, 1)] }, { coefficient := -1, powers := [(52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (59, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := -1, powers := [(42, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }, { coefficient := 1, powers := [(51, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (41, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (21, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1)] }, { coefficient := -1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (59, 1), (60, 1), (68, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (15, 1), (42, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (15, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := -1, powers := [(15, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (36, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (15, 1), (36, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (36, 1), (42, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (36, 1), (51, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (33, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (36, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_6_1_5_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_6_1_5_3
