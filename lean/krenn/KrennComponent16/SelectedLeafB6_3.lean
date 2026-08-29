import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "515780b9d131c1d2d6a98447eac312b91b39c825a64dd4f737e7a79b8a541d25"
def certificateSHA256 : String := "d7b704dc4ea6a3e899dc3637e0afecb4ad65d0668cb3561d8a33111c6bbf0eda"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 668 := ![
  0,
  1,
  2,
  3,
  4,
  6,
  23,
  24,
  30,
  33,
  302,
  314,
  316,
  328,
  348,
  366,
  408,
  440,
  571,
  654,
  661,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (43, 1), (61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (43, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (43, 1), (61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (50, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (43, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (43, 1), (60, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (43, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (31, 1), (43, 2), (53, 2), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (43, 2), (53, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(19, 1), (43, 2), (58, 1), (64, 1), (65, 2)] }, { coefficient := -1, powers := [(20, 1), (43, 2), (54, 1), (64, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (43, 1), (54, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (31, 1), (43, 2), (53, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (43, 2), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 2), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (43, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 2), (53, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 2), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (43, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (55, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (40, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (43, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (43, 1), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(42, 1), (43, 2), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 2), (48, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 2), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (43, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 2), (58, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (31, 1), (43, 2), (53, 2), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 2), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (43, 2), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_3
