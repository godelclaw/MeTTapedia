import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "26205f417ceedc75727d35547f3a0325271464b336430e9797cbe8eb5f856018"
def certificateSHA256 : String := "02d3e2db90708aa0b9e512296663410f801f4dc0fbd4cbc0c3a18a1a7bf70b05"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 672 := ![
  9,
  10,
  12,
  15,
  19,
  24,
  139,
  140,
  164,
  253,
  272,
  276,
  302,
  303,
  305,
  307,
  375,
  403,
  448,
  451,
  549,
  608,
  661,
  662,
  664,
  665,
  667,
  668,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (38, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 2, powers := [(11, 1), (32, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (26, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (26, 1), (29, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (31, 1), (37, 1), (53, 1)] }, { coefficient := -2, powers := [(11, 1), (29, 1), (34, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (31, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(11, 1), (43, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (45, 1), (46, 1), (54, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (45, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (18, 1), (32, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (32, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (26, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := -2, powers := [(11, 1), (29, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (37, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := 3, powers := [(11, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(11, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (45, 1), (54, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (31, 1), (37, 1)] }, { coefficient := 2, powers := [(11, 1), (29, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (31, 1), (37, 1)] }, { coefficient := 2, powers := [(11, 1), (23, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (45, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (37, 1)] }, { coefficient := -2, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (41, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (26, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (37, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := 2, powers := [(11, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -2, powers := [(11, 1), (34, 1), (37, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (23, 1), (24, 1), (26, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (18, 1), (24, 1), (26, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1)] }, { coefficient := 1, powers := [(11, 1), (18, 1), (23, 1), (24, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := 2, powers := [(11, 1), (18, 1), (23, 1), (24, 1), (34, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (24, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -3, powers := [(11, 1), (18, 1), (24, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (23, 1), (24, 1), (31, 1), (37, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (31, 1), (32, 1), (37, 1), (38, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (24, 1), (32, 1), (34, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (26, 1), (45, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (26, 1), (45, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (26, 1), (35, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (31, 1), (35, 1), (37, 1)] }, { coefficient := 2, powers := [(8, 1), (11, 1), (34, 1), (35, 1), (37, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (31, 1), (35, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (13, 1), (19, 1), (26, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (19, 1), (26, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (13, 1), (19, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := 2, powers := [(11, 1), (13, 1), (19, 1), (29, 1), (34, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(11, 1), (13, 1), (19, 1), (31, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := -2, powers := [(11, 1), (13, 1), (19, 1), (34, 1), (35, 1), (37, 1), (38, 1)] }, { coefficient := 2, powers := [(11, 1), (21, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (19, 1), (29, 1), (31, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (19, 1), (31, 1), (35, 1), (37, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (26, 1), (45, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_4_1.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_4_1
