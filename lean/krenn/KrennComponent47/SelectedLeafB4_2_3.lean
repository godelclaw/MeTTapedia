import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component47.SelectedLeafB4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6c8ac32faf506930f88cb4095c7bc34d8d5f7559784886e2ddbc88ad1a67e04c"
def certificateSHA256 : String := "41d7656716f83e25060f74e31d2803e86c1d6cedb3a84c81a0eb543aff26418f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 596 := ![
  2,
  6,
  32,
  34,
  35,
  210,
  250,
  272,
  376,
  377,
  470,
  529,
  576,
  586,
  587,
  589,
  591,
  592,
  595
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (43, 1), (56, 2), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (56, 2)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (37, 1), (56, 2), (59, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (43, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (46, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (43, 1), (45, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (45, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (37, 1), (45, 1), (54, 1), (59, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (43, 1), (51, 1), (56, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (51, 1), (56, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (37, 1), (51, 1), (56, 1), (58, 1), (59, 2), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(49, 1), (61, 1)] }, { coefficient := -1, powers := [(53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (18, 1), (32, 1), (43, 1), (49, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (32, 1), (43, 1), (53, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (53, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (37, 1), (49, 1), (54, 1), (59, 2), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (37, 1), (53, 1), (54, 1), (59, 2), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (43, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (37, 1), (56, 1), (58, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (56, 1), (58, 1), (59, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (49, 1), (58, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (53, 1), (58, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (43, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (56, 1), (57, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (19, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (56, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (14, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (14, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1), (56, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (54, 1), (59, 2)] }],
  [{ coefficient := -1, powers := [(43, 1), (59, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1)] }, { coefficient := -1, powers := [(37, 1), (56, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (40, 1), (54, 1), (56, 1), (59, 2), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (49, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (43, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (37, 1), (51, 1), (56, 1), (59, 2)] }, { coefficient := 1, powers := [(37, 1), (56, 1), (59, 2)] }, { coefficient := 1, powers := [(49, 1), (59, 1)] }, { coefficient := 1, powers := [(53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (38, 1), (43, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (43, 1), (46, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1), (56, 1), (57, 1), (59, 2)] }, { coefficient := 1, powers := [(37, 1), (46, 1), (51, 1), (56, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (43, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (37, 1), (54, 1), (56, 1), (59, 2)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (35, 1), (43, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (56, 1), (59, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (40, 1), (56, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (56, 1), (58, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (53, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (35, 1), (43, 1), (51, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (35, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (32, 1), (43, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (21, 1), (32, 1), (43, 1), (53, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (32, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (32, 1), (53, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (32, 1), (43, 1), (45, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (32, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (35, 1), (37, 1), (51, 1), (56, 1), (58, 1), (59, 2)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (32, 1), (37, 1), (49, 1), (54, 1), (59, 2)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (32, 1), (37, 1), (53, 1), (54, 1), (59, 2)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (37, 1), (45, 1), (54, 1), (59, 2)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component47.SelectedLeafB4_2_3.selectedHasNoCommonZero

end Krenn.Component47.SelectedLeafB4_2_3
