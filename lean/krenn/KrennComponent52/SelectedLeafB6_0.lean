import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component52.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "944df6eb9cb2571cc6fd6cdb394d00ee4d5d7670743454756dd168296cde9637"
def certificateSHA256 : String := "ff63ddc5b8fd7a18d4e4f3ff462b5a4e6273febe8a9cdb62f8b0d810622b0170"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 640 := ![
  8,
  11,
  17,
  24,
  26,
  34,
  161,
  166,
  184,
  293,
  313,
  346,
  347,
  352,
  353,
  354,
  355,
  460,
  461,
  467,
  473,
  555,
  633,
  636,
  638,
  639
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (32, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (44, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (44, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (23, 1), (44, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (24, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (52, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (23, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (19, 1), (23, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (24, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (50, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (23, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(6, 1), (23, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(23, 1), (24, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(6, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (47, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (44, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (47, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (29, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (32, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (38, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (46, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (24, 1), (32, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (29, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (23, 1), (24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 2), (32, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := -2, powers := [(6, 1), (18, 1), (23, 1), (24, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(13, 1), (24, 1), (29, 1), (47, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (24, 2), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (44, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (29, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (35, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (29, 1), (44, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component52.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component52.SelectedLeafB6_0
