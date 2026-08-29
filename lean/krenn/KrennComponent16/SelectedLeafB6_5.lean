import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "66019b995eac5942c45e6e5d396e5626ad2da65806e38a33bcfeb324cd25073f"
def certificateSHA256 : String := "cd09dd90f1d92fc9d6360ea70438e4e7f107c1fefa0b4545f74866ed6fa1c824"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 668 := ![
  1,
  2,
  3,
  13,
  23,
  24,
  33,
  302,
  304,
  316,
  408,
  428,
  440,
  442,
  448,
  468,
  505,
  571,
  612,
  656,
  661,
  663,
  664,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1)] }, { coefficient := 1, powers := [(24, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (27, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(13, 1), (31, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (37, 1), (38, 1), (43, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (31, 1), (43, 1), (48, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1), (48, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (43, 1), (54, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (31, 1), (43, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (37, 1), (38, 1), (43, 1), (54, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (43, 1), (45, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (25, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (26, 1), (31, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (27, 1), (34, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (34, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (26, 1), (31, 1), (43, 1), (48, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (43, 1), (45, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (26, 1), (27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(19, 1), (26, 1), (31, 1), (43, 1), (48, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB6_5
