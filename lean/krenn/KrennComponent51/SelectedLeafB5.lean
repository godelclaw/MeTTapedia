import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component51.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d04c1ab35199e7ddf4ad98147980e2bca990155c4410f710406e5f2dc024c1a1"
def certificateSHA256 : String := "612e593f76e8b194963d19ecf1e59b54175c5436618ab861bec52b8371444d2f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 606 := ![
  2,
  4,
  13,
  28,
  32,
  36,
  54,
  64,
  163,
  168,
  170,
  171,
  172,
  173,
  174,
  176,
  177,
  179,
  200,
  204,
  205,
  222,
  223,
  240,
  258,
  372,
  373,
  374,
  375,
  378,
  383,
  384,
  386,
  388,
  424,
  433,
  450,
  512,
  557,
  602,
  603,
  605
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 61) := ![
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (24, 1), (28, 1), (40, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (28, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (20, 1), (28, 1), (40, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (27, 1), (45, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (43, 1), (55, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := -2, powers := [(2, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (18, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (35, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (40, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(6, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (31, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (45, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(35, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (40, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(18, 1), (40, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (31, 1), (35, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (31, 1), (35, 2), (40, 1), (55, 2), (57, 1)] }, { coefficient := 2, powers := [(28, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(31, 1), (35, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (18, 1), (40, 1), (45, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (40, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (35, 1), (40, 1), (45, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (19, 1), (37, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(18, 1), (45, 1), (55, 1)] }],
  [{ coefficient := -4, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 2, powers := [(23, 1), (35, 1), (58, 1)] }, { coefficient := -2, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (18, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (8, 1), (31, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (5, 1), (31, 1), (40, 1), (55, 2), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (31, 1), (35, 1), (40, 1), (55, 2), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (31, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 2, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (58, 1)] }],
  [{ coefficient := 4, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (40, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (35, 1), (40, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(52, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (40, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (35, 1), (40, 1), (46, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (28, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (28, 1), (35, 1), (40, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (19, 1), (35, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (13, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (28, 1), (40, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (6, 1), (40, 1), (55, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (5, 1), (40, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (8, 1), (40, 1), (55, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (8, 1), (31, 1), (46, 1), (49, 1)] }, { coefficient := 2, powers := [(2, 2), (6, 1), (37, 1), (40, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 2), (6, 1), (40, 2), (55, 2), (57, 1)] }, { coefficient := 2, powers := [(2, 2), (6, 1), (40, 1), (46, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (28, 1), (35, 1), (40, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (40, 1), (43, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (8, 1), (31, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (5, 1), (31, 1), (35, 1), (40, 1), (55, 2), (57, 2)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (5, 1), (31, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (31, 1), (35, 2), (40, 1), (55, 2), (57, 2)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (31, 1), (35, 1), (40, 1), (55, 2), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (45, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (35, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (34, 1), (40, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component51.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component51.SelectedLeafB5
