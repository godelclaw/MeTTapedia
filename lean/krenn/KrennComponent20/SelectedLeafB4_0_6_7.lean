import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_0_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5376dd121451b8eae8b0250e3ebb92fad0a12234c973b4d00c5c9c263e459314"
def certificateSHA256 : String := "3c99f0391504eb0269905de5b9b914dfa3c07b9af822fc3980fef52efd9a4dc9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 648 := ![
  7,
  13,
  20,
  28,
  31,
  32,
  194,
  315,
  348,
  349,
  352,
  353,
  405,
  470,
  522,
  580,
  634,
  635,
  637,
  638,
  640,
  641,
  644,
  646,
  647
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (38, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (27, 1), (35, 1), (51, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (21, 1), (27, 1), (35, 1), (53, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (35, 1), (51, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (35, 1), (53, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (27, 1), (35, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (22, 1), (35, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (35, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (35, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (35, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (27, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (45, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (27, 1), (29, 1), (35, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (21, 1), (27, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (27, 1), (35, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (22, 1), (35, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (21, 1), (22, 1), (35, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (22, 1), (35, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (35, 1), (45, 1), (53, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_0_6_7.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_0_6_7
