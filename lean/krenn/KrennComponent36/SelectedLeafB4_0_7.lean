import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7092ea6d718ab255b0aaa6b08a6e68b169846dca26641ca310dcb3f01de8bd53"
def certificateSHA256 : String := "545f7233cbbfa180ffd1e5e6760a8f37e60d7d1eaef31ae6e3d0de34897929fc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 672 := ![
  9,
  10,
  13,
  14,
  15,
  24,
  160,
  256,
  272,
  276,
  302,
  303,
  305,
  307,
  363,
  373,
  451,
  488,
  562,
  607,
  608,
  661,
  662,
  664,
  665,
  667,
  668,
  669,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (37, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (29, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (43, 1), (44, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (48, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (29, 1), (43, 1), (45, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (32, 1), (43, 1), (45, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (43, 1), (47, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (29, 1), (45, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (32, 1), (45, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (57, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (43, 1), (47, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (32, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (32, 1), (45, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (37, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (40, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (45, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (37, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (40, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (45, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (43, 1), (47, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (48, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (34, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (34, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (29, 1), (61, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (24, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (22, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(13, 1), (22, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (29, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (45, 1), (58, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_0_7.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_0_7
