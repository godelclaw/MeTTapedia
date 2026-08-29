import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_2_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f9fd387c71c2d471f989841ef472d60bbbad70bb8fc1a3de0d75e144c4fe555e"
def certificateSHA256 : String := "b10657143bd259c8a783f3ad91ddb5e05878596a3cdd0e7ce9734d5de93c8d2c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 670 := ![
  2,
  9,
  10,
  19,
  24,
  147,
  162,
  167,
  168,
  246,
  294,
  295,
  318,
  323,
  403,
  409,
  433,
  437,
  438,
  443,
  478,
  479,
  501,
  562,
  604,
  606,
  607,
  656,
  657,
  658,
  659,
  663,
  665,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(7, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (22, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (52, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (52, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(29, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (40, 1), (59, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (34, 1), (52, 2), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (52, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (34, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (19, 1), (37, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (27, 1), (34, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (22, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (23, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (19, 1), (24, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (29, 1), (40, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (22, 1), (34, 1), (52, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (27, 1), (34, 1), (52, 2), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (36, 1), (39, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (22, 1), (34, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (27, 1), (34, 1), (46, 1), (52, 2), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (36, 1), (39, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (22, 1), (34, 1), (42, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (27, 1), (34, 1), (42, 1), (52, 2), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (15, 1), (34, 1), (36, 1), (39, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (34, 1), (40, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (34, 1), (40, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (23, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (29, 1), (40, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (34, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (34, 1), (46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(13, 1), (49, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_2_1_0.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_2_1_0
