import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component53.SelectedLeafB4_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f32b206e4550362c49fc4d0a5e13c1ba24f2b544277314e41d7ce3c592b540d4"
def certificateSHA256 : String := "a0764ff81540f7b5ef799b52eb151014534296ae3c0d94be3b66667e1be2c707"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 646 := ![
  2,
  4,
  23,
  163,
  164,
  169,
  170,
  192,
  198,
  230,
  348,
  355,
  359,
  360,
  361,
  434,
  458,
  464,
  477,
  636,
  637,
  639,
  641,
  642,
  644,
  645
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (54, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (52, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (27, 1), (52, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (26, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (26, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (31, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (34, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (25, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (22, 1), (25, 1), (26, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (22, 1), (25, 1), (27, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(21, 1), (22, 1), (25, 1), (54, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component53.SelectedLeafB4_0_3.selectedHasNoCommonZero

end Krenn.Component53.SelectedLeafB4_0_3
