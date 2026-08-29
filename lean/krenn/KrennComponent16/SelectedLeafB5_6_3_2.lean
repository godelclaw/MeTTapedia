import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_3_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ee52ba69bc00cd47fa20ec173ea0795d91bdf0126f93f5c43e50c1ec3a24ed9b"
def certificateSHA256 : String := "b19e07cd16c21945a047ec6e79f1344988e8df74078da2c589ebadd47d997f34"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 674 := ![
  10,
  13,
  18,
  23,
  27,
  29,
  142,
  162,
  170,
  171,
  316,
  408,
  436,
  440,
  448,
  571,
  588,
  595,
  661,
  662,
  667,
  669,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (58, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1), (58, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (55, 1), (62, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (55, 1), (62, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (49, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (50, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_3_2.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_3_2
