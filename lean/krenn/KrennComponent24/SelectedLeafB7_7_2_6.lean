import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB7_7_2_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7096af2456add87e0055045ed9cad33ca09501e6a01ee90a707a11c3ab5854fc"
def certificateSHA256 : String := "d16adec48e19f18edc64db7ab84bb62ce6100e8737671cd6b85540c20c02d4ca"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 676 := ![
  13,
  129,
  143,
  159,
  307,
  323,
  457,
  471,
  594,
  597,
  663,
  665,
  667,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (22, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (48, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (43, 1), (45, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(19, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1), (51, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB7_7_2_6.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB7_7_2_6
