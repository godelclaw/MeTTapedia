import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component46.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "864fa62d339a9979dc38c84b43d3fa7d9b00636b2bfa6dc1f033f0474a3c71de"
def certificateSHA256 : String := "ac07754154732381eedcd7af3d525262a851b6d010fa821cce518c2147590b34"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 643 := ![
  2,
  3,
  5,
  12,
  21,
  23,
  24,
  29,
  42,
  162,
  163,
  166,
  168,
  169,
  170,
  197,
  202,
  210,
  216,
  220,
  240,
  327,
  350,
  352,
  357,
  359,
  361,
  362,
  363,
  365,
  434,
  444,
  466,
  467,
  480,
  562,
  574,
  587,
  639,
  640,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (22, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (27, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (27, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (26, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 63) := ![
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (27, 1), (40, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (40, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 2), (40, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (22, 1), (40, 1), (59, 1), (61, 1)] }, { coefficient := -4, powers := [(8, 1), (26, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(34, 1), (38, 1), (49, 1)] }, { coefficient := -2, powers := [(37, 1), (38, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (30, 1), (48, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(26, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(26, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(31, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (30, 1), (34, 1), (62, 1)] }, { coefficient := 2, powers := [(3, 1), (34, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := -2, powers := [(14, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (20, 1), (34, 1), (52, 1)] }, { coefficient := 2, powers := [(3, 1), (20, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(21, 1), (31, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (31, 1), (52, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (23, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (48, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (23, 1), (53, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (53, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (34, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (27, 1), (48, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (26, 1), (53, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(26, 1), (53, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (22, 1), (23, 1), (57, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(14, 1), (31, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (40, 1), (56, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(2, 1), (40, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (49, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (37, 1), (43, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(54, 1)] }],
  [{ coefficient := -2, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (23, 1), (30, 1), (57, 1), (62, 1)] }, { coefficient := 2, powers := [(26, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(27, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(21, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (22, 1), (40, 1), (56, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (56, 1), (59, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (27, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(26, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (34, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(31, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (23, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (22, 1), (38, 1), (40, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (43, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (27, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (40, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (22, 1), (23, 1), (46, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (22, 1), (38, 1), (40, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (22, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (22, 1), (48, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (40, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := -2, powers := [(8, 1), (37, 1), (38, 1), (43, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (37, 1), (43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component46.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component46.SelectedLeafB5
