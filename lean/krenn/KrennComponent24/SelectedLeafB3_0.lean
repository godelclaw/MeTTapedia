import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c476d02ba9fe54a5878e668314be575c5715e6249ee8ee90de9c1172670db782"
def certificateSHA256 : String := "14c21e96d706e2030a62dfd0802d6aaaf17800ccf442d9f51a699620c95ca3c7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 670 := ![
  13,
  15,
  23,
  129,
  143,
  153,
  164,
  166,
  167,
  299,
  307,
  316,
  323,
  417,
  425,
  441,
  449,
  457,
  471,
  472,
  474,
  478,
  541,
  584,
  585,
  594,
  652,
  663,
  664,
  665,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }, { coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (31, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (31, 1), (57, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (20, 1), (26, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (20, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (18, 1), (20, 1), (30, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (20, 1), (31, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (20, 1), (31, 1), (39, 1), (60, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (20, 1), (31, 1), (46, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (20, 1), (30, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (39, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (31, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (47, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (46, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (5, 1), (20, 1), (31, 1), (57, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (20, 1), (31, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (31, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB3_0.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB3_0
