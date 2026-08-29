import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_2_1_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "93c5d742cdda663fffc6e9b0defdd214b68553cbdd327157eb058e1e075869af"
def certificateSHA256 : String := "9e1b017f9674f103ea75ba1de2e65e6deda29e0d5b88a3dcd903008451187b34"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 674 := ![
  9,
  13,
  18,
  21,
  23,
  29,
  32,
  170,
  171,
  273,
  316,
  433,
  436,
  440,
  448,
  454,
  481,
  571,
  609,
  661,
  664,
  666,
  667,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(25, 1), (33, 1), (39, 1), (58, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (39, 1), (58, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (39, 1), (40, 1), (64, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1), (39, 1), (40, 1), (64, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (27, 1), (33, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (36, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (33, 1), (40, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (40, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (39, 1), (45, 1), (55, 1), (64, 1), (67, 2)] }, { coefficient := -1, powers := [(25, 1), (36, 1), (39, 1), (45, 1), (55, 1), (64, 1), (67, 2)] }, { coefficient := -1, powers := [(29, 1), (53, 1), (63, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (63, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (53, 1), (64, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (39, 1), (55, 1), (64, 1), (67, 2)] }, { coefficient := 1, powers := [(2, 1), (36, 1), (39, 1), (55, 1), (64, 1), (67, 2)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (33, 1), (40, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (40, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (33, 1), (39, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (39, 1), (55, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (39, 1), (45, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1), (45, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (64, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (33, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (39, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (55, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (36, 1), (39, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(36, 1), (40, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (33, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (39, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (33, 1), (39, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (39, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (37, 1), (39, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (37, 1), (39, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (33, 1), (39, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (36, 1), (39, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (39, 1), (40, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (37, 1), (39, 1), (40, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (33, 1), (39, 1), (50, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (39, 1), (50, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (33, 1), (39, 1), (45, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (36, 1), (39, 1), (45, 1), (55, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [(47, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (39, 1), (61, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (39, 1), (61, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (33, 1), (39, 1), (45, 1), (49, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (36, 1), (39, 1), (45, 1), (49, 1), (64, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1), (50, 1), (64, 1), (67, 1)] }, { coefficient := -2, powers := [(20, 1), (33, 1), (39, 1), (43, 1), (64, 1), (67, 1)] }, { coefficient := -2, powers := [(20, 1), (36, 1), (39, 1), (43, 1), (64, 1), (67, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_2_1_6.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_2_1_6
