import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB4_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d692cc85d601b0a944ebed9359ad1fa605860549a7a1194298d3e44a34b87810"
def certificateSHA256 : String := "f312029aa2b358fac4368a2755fb5a85bf639b5f35d3b0363eadbc38cb21cfb8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 643 := ![
  13,
  16,
  195,
  313,
  343,
  348,
  349,
  350,
  351,
  360,
  365,
  524,
  633,
  636,
  638,
  639,
  642
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(12, 1), (28, 2), (46, 2), (50, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (28, 2), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 2), (18, 1), (28, 2), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(12, 2), (28, 2), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (46, 2)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 2), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 2), (28, 2), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(12, 1), (28, 1), (37, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (40, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 2), (52, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 2), (18, 1), (28, 2), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (22, 1), (23, 1), (28, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (22, 1), (23, 1), (28, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (23, 1), (28, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (22, 1), (42, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (23, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (12, 1), (28, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (16, 1), (28, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (28, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB4_4_2.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB4_4_2
