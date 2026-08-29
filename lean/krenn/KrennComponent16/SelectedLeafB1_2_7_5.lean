import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component16.SelectedLeafB1_2_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "90a4bd440cfd6f10940dc11e7fd3a41feb12f8d3f96f60078d2e8637c419341b"
def certificateSHA256 : String := "fad6fce67cc6bdd07d10755da2cc1b2875676142c47834030cc6da3aea51f900"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 674 := ![
  9,
  12,
  13,
  23,
  166,
  175,
  302,
  313,
  316,
  407,
  440,
  448,
  454,
  455,
  478,
  479,
  501,
  527,
  584,
  585,
  594,
  661,
  662,
  664,
  667,
  668,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1)] }, { coefficient := 1, powers := [(22, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (22, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (38, 1), (40, 1), (50, 1), (60, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (58, 1), (64, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (50, 1), (67, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (29, 1), (40, 2), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (27, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (40, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (30, 1), (40, 1), (42, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (30, 1), (40, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (40, 1), (42, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (40, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (25, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (37, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (31, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (58, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (30, 1), (40, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (40, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (30, 1), (40, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (29, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (40, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (25, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (24, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (21, 2), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (40, 2), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (21, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (26, 1), (30, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (21, 1), (30, 1), (40, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (25, 1), (38, 1), (47, 1), (55, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (37, 1), (38, 1), (40, 1), (47, 1), (55, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (21, 1), (30, 1), (40, 1), (53, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (26, 1), (30, 1), (40, 1), (47, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (37, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (47, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (38, 1), (40, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (31, 1), (38, 1), (58, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (8, 1), (37, 1), (38, 1), (40, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (13, 1), (31, 1), (38, 1), (40, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (14, 1), (25, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (50, 1)] }, { coefficient := -1, powers := [(13, 1), (37, 1), (40, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component16.SelectedLeafB1_2_7_5.selectedHasNoCommonZero

end Krenn.Component16.SelectedLeafB1_2_7_5
