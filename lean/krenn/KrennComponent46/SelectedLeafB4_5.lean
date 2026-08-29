import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component46.SelectedLeafB4_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "277045dc2b21e1a8aa9732609e020ca75bf58ff92da7cf53d98073b206ee0770"
def certificateSHA256 : String := "27503eb6273bdc44448a9dea96fee63fa4cb0589b7df3c234a9d78b26e1871b4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 646 := ![
  3,
  22,
  29,
  162,
  204,
  207,
  240,
  330,
  350,
  352,
  361,
  362,
  387,
  561,
  639,
  640,
  642,
  643,
  644,
  645
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(8, 1), (26, 1), (43, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (43, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (49, 1), (61, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (43, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (43, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(43, 2), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (43, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (26, 1), (43, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (34, 1), (43, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component46.SelectedLeafB4_5.selectedHasNoCommonZero

end Krenn.Component46.SelectedLeafB4_5
