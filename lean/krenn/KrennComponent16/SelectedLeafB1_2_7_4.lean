import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB1_2_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cf1083b865d17db70afd2c4eefacf81f46547abe38a8a14964a69ef02b17ae28"
def certificateSHA256 : String := "9dbdaaccd7bd5c7cfe0140c0fc9b7e136f5a1c877c48f189ee92a17f37bf70d1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 674 := ![
  7,
  9,
  13,
  21,
  23,
  32,
  53,
  147,
  171,
  175,
  273,
  300,
  301,
  316,
  440,
  448,
  481,
  506,
  571,
  593,
  608,
  609,
  649,
  660,
  661,
  662,
  663,
  667,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(47, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (36, 1), (42, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (33, 1), (39, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (37, 1), (39, 1), (40, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (33, 1), (39, 1), (58, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (37, 1), (39, 1), (40, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (25, 1), (27, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(11, 1), (30, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (30, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -2, powers := [(11, 1), (42, 1), (45, 1), (66, 1)] }, { coefficient := -2, powers := [(11, 1), (45, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (45, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (19, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (33, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (40, 1), (42, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (26, 1), (36, 1), (40, 1), (42, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (33, 1), (39, 1), (45, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (25, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 2, powers := [(11, 1), (42, 1), (66, 1)] }, { coefficient := 2, powers := [(11, 1), (47, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (66, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (66, 1)] }, { coefficient := -1, powers := [(47, 1), (66, 1)] }, { coefficient := -1, powers := [(53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (36, 1), (37, 1), (42, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (25, 1), (36, 1), (42, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (25, 1), (33, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (25, 1), (33, 1), (39, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := 1, powers := [(42, 2), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (47, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (48, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (36, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (7, 1), (36, 1), (40, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (25, 1), (36, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (25, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (33, 1), (37, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (25, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (33, 1), (37, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (33, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (36, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (33, 1), (39, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (33, 1), (39, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (39, 1), (50, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB1_2_7_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB1_2_7_4
