import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_0_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "920615db67d26ffc0f76a279ec4a35a3a924391800c7642f5368df1b572a8325"
def certificateSHA256 : String := "81701d3df8ebf70cbf343410fa42dfd3e81953a599dbc5ea9e16887351a4b864"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 667 := ![
  0,
  7,
  9,
  10,
  19,
  142,
  162,
  163,
  167,
  270,
  294,
  295,
  301,
  315,
  318,
  409,
  433,
  437,
  443,
  531,
  562,
  581,
  657,
  658,
  660,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(31, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (56, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (26, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(43, 1), (57, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (18, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_0_2.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_0_2
