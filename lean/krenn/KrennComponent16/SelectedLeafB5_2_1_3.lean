import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a077b92fc5fd3844a8015c96b2167b70c4aa57385c28452388646ad5950db7a9"
def certificateSHA256 : String := "1a555465b4cf1cc5ea5d735379f1730eda2682641616ad04edcd7b527d90101c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 674 := ![
  10,
  13,
  18,
  21,
  23,
  29,
  32,
  170,
  273,
  302,
  316,
  408,
  428,
  433,
  436,
  440,
  448,
  454,
  468,
  481,
  609,
  612,
  661,
  664,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (33, 1), (39, 1), (50, 1), (66, 2)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (36, 1), (39, 1), (50, 1), (66, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (27, 1), (36, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (33, 1), (40, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (40, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (33, 1), (39, 1), (45, 1), (55, 1), (66, 2)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (36, 1), (39, 1), (45, 1), (55, 1), (66, 2)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (53, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (39, 1), (50, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (33, 1), (39, 1), (55, 1), (66, 2)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (36, 1), (39, 1), (55, 1), (66, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (33, 1), (40, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (36, 1), (40, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (33, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (36, 1), (39, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (65, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (31, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (25, 1), (33, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(0, 1), (25, 1), (36, 1), (39, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (50, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (40, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (40, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (33, 1), (39, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (39, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (31, 1), (33, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (31, 1), (36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (33, 1), (39, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (25, 1), (36, 1), (39, 1), (48, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (33, 1), (39, 1), (42, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(0, 1), (20, 1), (25, 1), (36, 1), (39, 1), (42, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(27, 1), (42, 1), (45, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (45, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (33, 1), (39, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (36, 1), (39, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (33, 1), (39, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (36, 1), (39, 1), (50, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (33, 1), (39, 1), (45, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (25, 1), (36, 1), (39, 1), (45, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_1_3.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_1_3
