import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "727d8d4717a8d44838d8da5839dcce8b75652b8eb3cb632c4db2fe3827536fd9"
def certificateSHA256 : String := "a45a525483a8c8158a751b3188872d4100887a808146cbcde72771cac24cabbf"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 566 := ![
  4,
  30,
  40,
  42,
  46,
  200,
  201,
  243,
  244,
  249,
  252,
  283,
  284,
  360,
  378,
  379,
  380,
  386,
  388,
  400,
  513,
  549,
  559,
  560,
  561,
  562,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (24, 1), (35, 1), (55, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (24, 1), (52, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (45, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (33, 1), (35, 1), (46, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (46, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (44, 1), (49, 1), (57, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (15, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (11, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (33, 1), (35, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (16, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (5, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (49, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (35, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (33, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (36, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (49, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (33, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (33, 1), (35, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (5, 1), (30, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (24, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (25, 1), (49, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (26, 1), (33, 1), (45, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (25, 1), (33, 1), (35, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (25, 1), (33, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (21, 1), (25, 1), (44, 1), (49, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB6_1
