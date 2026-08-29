import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component14.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "118b21044cf1b1e5f69459a1c2c2c23bd3bf9d3034a0b55cd5524b23fbf90d2f"
def certificateSHA256 : String := "a5bb29d649c9f60316f164105feedda534b6c56b6eddaaab504beb067eb8fa4c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 637 := ![
  1,
  3,
  6,
  9,
  166,
  179,
  183,
  193,
  195,
  208,
  282,
  313,
  342,
  343,
  348,
  350,
  360,
  365,
  406,
  464,
  488,
  555,
  633,
  634,
  636
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (40, 1), (42, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (40, 1), (42, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (42, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (23, 1), (42, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (35, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (58, 1)] }, { coefficient := -1, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (51, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (50, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (44, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (40, 1), (42, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (40, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (42, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(12, 1), (17, 1), (34, 1), (37, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (42, 1), (50, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (50, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component14.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component14.SelectedLeafB3
