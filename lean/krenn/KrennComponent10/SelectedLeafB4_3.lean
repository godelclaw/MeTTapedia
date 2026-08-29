import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "917bf99bedf75eb09caba966c0164779c285f082a85a8e361e90fc1e0df6470b"
def certificateSHA256 : String := "0d746c69c21de6fa448320234a32fd1e41c444323795a0642b5bef25531c0278"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 44 → Fin 641 := ![
  0,
  2,
  3,
  13,
  21,
  23,
  24,
  25,
  26,
  28,
  30,
  161,
  162,
  163,
  164,
  166,
  167,
  177,
  186,
  189,
  192,
  356,
  359,
  361,
  369,
  373,
  375,
  398,
  409,
  446,
  466,
  513,
  550,
  557,
  581,
  582,
  628,
  633,
  634,
  635,
  636,
  637,
  639,
  640
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 44 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 44 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (21, 1), (32, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (34, 1), (37, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (35, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (35, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (29, 1), (51, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (58, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 2, powers := [(18, 1), (29, 1), (41, 1), (51, 2), (61, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (5, 1), (32, 1), (56, 1), (58, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (11, 1), (32, 1), (45, 1), (56, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (29, 1), (51, 1), (59, 1), (62, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (32, 1), (45, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (16, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (34, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (31, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (27, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (43, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (21, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (41, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (35, 1), (41, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (34, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (21, 1), (32, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(5, 1), (19, 1), (21, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(28, 1), (41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (29, 1), (59, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (29, 1), (41, 1), (51, 1), (61, 1)] }, { coefficient := -2, powers := [(29, 1), (41, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (29, 1), (51, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (41, 1), (51, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (53, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (15, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(41, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(5, 1), (11, 1), (21, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (41, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 2, powers := [(8, 1), (27, 1), (47, 1), (59, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (41, 1), (51, 1), (55, 1), (59, 1), (62, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (37, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (40, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (45, 1), (51, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (45, 1), (51, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (59, 1)] }, { coefficient := -2, powers := [(40, 1), (41, 1), (56, 1), (61, 1)] }, { coefficient := -2, powers := [(41, 1), (46, 1), (52, 1), (61, 1)] }, { coefficient := 2, powers := [(41, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (51, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (29, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (35, 1), (53, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (29, 1), (34, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (11, 1), (26, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (21, 1), (32, 1), (55, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (26, 1), (32, 1), (45, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (15, 1), (32, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (29, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (29, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (27, 1), (47, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (27, 1), (48, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (29, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (29, 1), (41, 1), (51, 2), (61, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 44,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB4_3
