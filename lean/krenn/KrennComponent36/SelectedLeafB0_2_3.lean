import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB0_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "00a7101409b22828447b9f43f8017babcc15d8ca4abfc8fb5b164a719250fb67"
def certificateSHA256 : String := "a88b8e960813b09e2efff31989cf2b26cfa166fb34e2c6d3138eeafe9201fd50"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 672 := ![
  9,
  10,
  15,
  18,
  19,
  24,
  54,
  134,
  152,
  158,
  160,
  276,
  301,
  302,
  303,
  305,
  307,
  323,
  373,
  448,
  451,
  453,
  488,
  562,
  607,
  608,
  612,
  651,
  661,
  662,
  663,
  664,
  665,
  668,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (29, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (32, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (29, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (40, 1), (58, 1)] }, { coefficient := 2, powers := [(11, 1), (29, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -2, powers := [(16, 1), (29, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (16, 1), (26, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (26, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (45, 1), (55, 1)] }, { coefficient := -1, powers := [(23, 1), (53, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (29, 1), (43, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (45, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (16, 1), (29, 1), (40, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (29, 1), (45, 2), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (29, 1), (45, 1), (52, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (40, 1), (45, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (45, 2), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (45, 1), (52, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (29, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (45, 1), (58, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (16, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (16, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (37, 1), (45, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (40, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (45, 2), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (37, 1), (45, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (40, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (45, 2), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (21, 1), (29, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (21, 1), (29, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (21, 1), (29, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (40, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (45, 2), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (45, 2), (58, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [(43, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (40, 1), (45, 1), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (45, 2), (61, 1)] }, { coefficient := 2, powers := [(3, 1), (5, 1), (16, 1), (29, 1), (31, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (40, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (45, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (16, 1), (31, 1), (32, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (21, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (45, 1), (58, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB0_2_3.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB0_2_3
