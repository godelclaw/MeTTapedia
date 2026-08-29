import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "599b2d30ff03bf2d2cc7c568c5dac7932dee785947f119e11f6ea7d10174822d"
def certificateSHA256 : String := "9f544ea3290745261b56f3efb5f649d14ed188ab452b6b215c488f09b0ba32dc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 664 := ![
  10,
  14,
  15,
  19,
  20,
  22,
  25,
  117,
  143,
  157,
  159,
  167,
  168,
  173,
  246,
  295,
  301,
  315,
  318,
  327,
  409,
  433,
  437,
  443,
  562,
  580,
  581,
  588,
  608,
  612,
  650,
  657,
  658,
  659,
  660,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (27, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (24, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (33, 1), (38, 1), (57, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (52, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(1, 1), (13, 1), (34, 1), (40, 1), (49, 1), (52, 1), (62, 1), (65, 2)] }, { coefficient := 1, powers := [(1, 1), (18, 1), (34, 1), (40, 1), (43, 1), (52, 1), (62, 1), (65, 2)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (42, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (46, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (52, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (56, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (49, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (52, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1), (52, 2), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (43, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (43, 1), (57, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (43, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (34, 1), (48, 1), (54, 1), (62, 1), (65, 2)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (48, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (49, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (48, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (13, 1), (34, 1), (40, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (34, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (25, 1), (34, 1), (40, 1), (43, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (54, 1)] }, { coefficient := -1, powers := [(25, 1), (31, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (31, 1), (43, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (13, 1), (34, 1), (40, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (40, 1), (43, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (25, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := -1, powers := [(42, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (57, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (25, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (34, 1), (45, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (13, 1), (25, 1), (34, 1), (40, 1), (49, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(1, 1), (18, 1), (25, 1), (34, 1), (40, 1), (43, 1), (52, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (21, 1), (24, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (15, 1), (24, 1), (33, 1), (38, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (42, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (52, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (24, 1), (25, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (25, 1), (31, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (31, 1), (43, 1), (52, 2), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (31, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (43, 1), (53, 1), (64, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB6_7.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB6_7
