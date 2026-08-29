import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dcb80f5cf4ffb0a1e75587569a28428d92689cc213ec2e8d2a6f2f57ad73d153"
def certificateSHA256 : String := "00a61c52abea889fe087927d4933ab59f084298eb7b0abad8205d42e7b7f848c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 674 := ![
  13,
  23,
  170,
  247,
  248,
  250,
  299,
  302,
  316,
  325,
  407,
  408,
  436,
  440,
  448,
  588,
  594,
  661,
  662,
  667,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (50, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (58, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1), (62, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (58, 1), (61, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 2), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (58, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 2), (66, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (31, 1), (50, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (21, 1), (37, 1), (40, 1), (58, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (50, 1), (53, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1), (58, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (42, 1), (45, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (45, 1), (47, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (48, 1), (55, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (42, 1), (55, 1), (58, 1), (66, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_5_1.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_5_1
