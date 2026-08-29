import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB4_6_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7380b562e93cacec44d708494ad800ec626ac5d0731065b7bd49483cdccba895"
def certificateSHA256 : String := "fde19ec6a8bed515acc16e8d943ba4fef0081565ca7dfa0d468406aafc5baf90"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 674 := ![
  9,
  13,
  18,
  23,
  27,
  162,
  170,
  244,
  302,
  316,
  436,
  440,
  448,
  595,
  661,
  664,
  665,
  667,
  669,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (58, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (58, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(31, 1), (50, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (25, 1), (55, 1), (63, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1), (63, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (25, 1), (28, 1), (55, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB4_6_7_7.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB4_6_7_7
