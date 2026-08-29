import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB5_6_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e86dfeaaf684d4a666f783e7274af8150450b0d912a04198dde3e933d5a1ea24"
def certificateSHA256 : String := "77981c8744d3d5538096172b96d9ca3ff4d2c1c35ed8ecff3ec08ec4bf2230c2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 674 := ![
  7,
  9,
  13,
  23,
  32,
  142,
  166,
  167,
  168,
  170,
  171,
  299,
  300,
  301,
  314,
  315,
  316,
  317,
  321,
  325,
  407,
  408,
  436,
  438,
  440,
  448,
  454,
  571,
  573,
  588,
  660,
  661,
  662,
  663,
  667,
  669,
  670,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (50, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (58, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (22, 1), (45, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (24, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (47, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (21, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (26, 1), (45, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (45, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (45, 1), (49, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -2, powers := [(26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (26, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (26, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (49, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (42, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (47, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (23, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (25, 1), (55, 1)] }, { coefficient := 2, powers := [(20, 1), (25, 1), (26, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (26, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (30, 1), (49, 1), (55, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (30, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (34, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (45, 1), (47, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (48, 1), (50, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (21, 1), (45, 1), (47, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (48, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(20, 1), (26, 1), (45, 1), (47, 1), (49, 1), (55, 1), (66, 1)] }, { coefficient := -2, powers := [(20, 1), (26, 1), (48, 1), (49, 1), (55, 1), (66, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB5_6_1_4.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB5_6_1_4
