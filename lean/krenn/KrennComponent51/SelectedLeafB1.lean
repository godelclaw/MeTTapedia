import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component51.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2d70a491dac357d84cd227fcfc491327ae09dee96ef3aaf497d9d95ac2a5134a"
def certificateSHA256 : String := "6884e592b692c499cd514406108c4a5134bdb2e4bf092cfb132329eef0127375"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 606 := ![
  2,
  4,
  170,
  173,
  176,
  179,
  205,
  216,
  222,
  223,
  240,
  258,
  383,
  384,
  390,
  392,
  557,
  602,
  603
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 60) := ![
  [{ coefficient := -2, powers := [(5, 1), (28, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (46, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -2, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(2, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(2, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (44, 1), (51, 1)] }, { coefficient := -2, powers := [(5, 1), (34, 1), (43, 1), (52, 1)] }, { coefficient := -2, powers := [(8, 1), (31, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (45, 1), (50, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component51.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component51.SelectedLeafB1
