import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB7_6_3_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "49584e38d36e4c0239dd8cccf974823fe294910b30cc70aea87d9bd4eb816915"
def certificateSHA256 : String := "5e84822bf06c00ccb93ddde252da4a57fe59f03fbcc4cfb29d58754b6c614213"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 670 := ![
  1,
  7,
  9,
  15,
  19,
  143,
  159,
  162,
  167,
  168,
  301,
  318,
  319,
  323,
  366,
  403,
  432,
  435,
  436,
  437,
  442,
  449,
  450,
  458,
  478,
  516,
  562,
  564,
  580,
  591,
  618,
  657,
  659,
  660,
  663,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (38, 1), (46, 1), (57, 1), (59, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (48, 1), (57, 1), (59, 1), (66, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (37, 1), (38, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (37, 1), (38, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (45, 1), (46, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (45, 2), (63, 1), (67, 2)] }],
  [{ coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (53, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (49, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (26, 1), (45, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (19, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (46, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (45, 1), (63, 1), (67, 2)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (30, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (37, 1), (38, 1), (54, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1)] }, { coefficient := -1, powers := [(26, 1), (45, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (37, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (38, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (38, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (38, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (30, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (30, 1), (45, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (38, 1), (46, 1), (57, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (38, 1), (48, 1), (57, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (19, 1), (45, 1), (46, 2), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (19, 1), (46, 1), (47, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (38, 1), (45, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (45, 2), (46, 1), (63, 1), (67, 2)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (45, 1), (47, 1), (63, 1), (67, 2)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (63, 1), (67, 1)] }]
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
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB7_6_3_4.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB7_6_3_4
