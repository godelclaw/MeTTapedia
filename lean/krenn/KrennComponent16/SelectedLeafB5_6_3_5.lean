import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6472336469b2bb8bffac097061919e639125e7b3d84d80ba906e43740328a628"
def certificateSHA256 : String := "780d35f755534cbfdc2b9f305eae892997e24972b2161e0dbcfff353951d9005"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 674 := ![
  5,
  9,
  13,
  21,
  142,
  273,
  300,
  301,
  302,
  317,
  321,
  362,
  448,
  512,
  518,
  588,
  591,
  593,
  608,
  609,
  660,
  661,
  662,
  663,
  665,
  667,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(5, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(11, 1), (37, 1), (39, 1), (53, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (37, 1), (39, 1), (53, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (33, 1), (37, 1), (39, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (37, 1), (39, 1), (40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (27, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1), (53, 1), (67, 1)] }, { coefficient := 2, powers := [(11, 1), (45, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (45, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (22, 1), (33, 1), (39, 1), (45, 1), (53, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (22, 1), (33, 1), (39, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (53, 1), (67, 1)] }, { coefficient := -2, powers := [(11, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (42, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (31, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (22, 1), (33, 1), (39, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (22, 1), (33, 1), (39, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (37, 1), (39, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(16, 1), (37, 1), (39, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (31, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(11, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (58, 1), (67, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (11, 1), (33, 1), (39, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (16, 1), (33, 1), (39, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (27, 1), (33, 1), (39, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (27, 1), (33, 1), (39, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (33, 1), (37, 1), (39, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (33, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (37, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (37, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (13, 1), (33, 1), (37, 1), (39, 1), (40, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (37, 1), (39, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (37, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (37, 1), (39, 1), (55, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(10, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (19, 1), (37, 1), (39, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1)] }, { coefficient := -1, powers := [(11, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (37, 1), (39, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (42, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (53, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_3_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_3_5
