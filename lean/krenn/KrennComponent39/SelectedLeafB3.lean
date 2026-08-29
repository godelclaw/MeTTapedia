import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b52356ff089948c47561d3222129857811cd4930e349cfae80719ebaf4dc8dee"
def certificateSHA256 : String := "d198a3bb4cd84612ba6e9dbf4a1185acd9743da33f966f72880dd893ff97a491"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 664 := ![
  1,
  2,
  3,
  4,
  6,
  7,
  8,
  9,
  184,
  193,
  326,
  430,
  434,
  440,
  458,
  467,
  566,
  607,
  608,
  660,
  661,
  662
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (19, 1), (34, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (46, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (28, 1), (51, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (34, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (39, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (34, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (34, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (45, 1)] }, { coefficient := -1, powers := [(12, 1), (28, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (28, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (46, 1), (49, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB3
