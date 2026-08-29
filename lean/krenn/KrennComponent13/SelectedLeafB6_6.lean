import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f8fb9465ee8cd0662a881416dd066e18f0036a563c13452452b3cf9e5c34e9c5"
def certificateSHA256 : String := "a93cf97d8afafb3a37344269d77bc980b38dc1a5e9a983fecba6b23a5748bccf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 611 := ![
  3,
  7,
  15,
  22,
  27,
  152,
  155,
  157,
  183,
  184,
  205,
  227,
  284,
  360,
  361,
  377,
  386,
  431,
  489,
  525,
  604,
  606,
  607,
  608,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (41, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(4, 1), (19, 1), (30, 1), (45, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (30, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (26, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (33, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (21, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (19, 1), (30, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (30, 1), (50, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (50, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (30, 1), (59, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (30, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (37, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB6_6.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB6_6
