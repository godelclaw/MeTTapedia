import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB4_7_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c7e080a9ddc2fdcadcc64a1776931211ed52a6673c8ea6a17a1529ac1abd9202"
def certificateSHA256 : String := "6bf04f2b90b9a6e50331eb2eaedaa224bcc168a7e2303f0b4746b6632af09171"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 676 := ![
  15,
  161,
  299,
  307,
  323,
  328,
  430,
  452,
  457,
  471,
  597,
  663,
  666,
  667,
  672,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (41, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (41, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (41, 1), (53, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (41, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(41, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1), (45, 1), (53, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(18, 1), (25, 1), (41, 1), (47, 1), (55, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (41, 1), (42, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (41, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (43, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (41, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (48, 1), (51, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB4_7_2_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB4_7_2_0
