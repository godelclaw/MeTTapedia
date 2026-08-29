import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_6_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3a450ae05b7698c1a2cffa177397edc8977a367ec0405b63e8b8274af9e51289"
def certificateSHA256 : String := "cfa3d42d3303de77d021a7050cadc870f85554708c5d6c86447464b3b8336aed"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 673 := ![
  14,
  26,
  232,
  280,
  304,
  305,
  476,
  478,
  511,
  603,
  659,
  662,
  664,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (42, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_6_3_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_6_3_0
