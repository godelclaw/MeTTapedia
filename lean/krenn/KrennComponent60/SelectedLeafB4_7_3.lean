import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f3c94aa2e837c188e2a73b4be2c0dc17be9ae5b41b98e34190a093c4f1907ee5"
def certificateSHA256 : String := "27d1510981ca3f8c56a25cc2f8987d40000f2d773933189e5bb51dc804476e88"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 665 := ![
  12,
  20,
  22,
  25,
  75,
  143,
  151,
  168,
  177,
  179,
  198,
  301,
  302,
  318,
  331,
  365,
  434,
  436,
  443,
  522,
  556,
  593,
  602,
  603,
  604,
  605,
  654,
  655,
  657,
  658,
  659,
  660,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(15, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 67) := ![
  [{ coefficient := 2, powers := [(6, 1), (12, 1), (31, 1), (40, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (31, 1), (51, 2), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (31, 1), (37, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (52, 1), (62, 1)] }, { coefficient := -2, powers := [(24, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(29, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (48, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (12, 1), (31, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (10, 1), (12, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(10, 1), (12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(9, 1), (12, 1), (48, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (12, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (12, 1), (31, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (40, 1), (57, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (20, 1), (31, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (20, 1), (31, 1), (51, 2), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := -4, powers := [(12, 1), (20, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (28, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (20, 1), (31, 1), (37, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (22, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (28, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (12, 1), (24, 1), (31, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (24, 1), (31, 1), (51, 2), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := 4, powers := [(12, 1), (24, 1), (28, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (28, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (31, 1), (37, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (51, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (24, 1), (31, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (27, 1), (51, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (28, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(10, 1), (12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (24, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -2, powers := [(12, 1), (24, 1), (37, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (39, 1), (40, 1), (56, 1), (57, 1), (62, 1)] }, { coefficient := -2, powers := [(12, 1), (24, 1), (40, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (45, 1), (51, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (51, 2), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(41, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (12, 1), (24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 2, powers := [(12, 1), (15, 1), (24, 1), (28, 1), (40, 1), (57, 1)] }, { coefficient := 2, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (29, 1), (52, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (52, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (12, 1), (29, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (57, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_7_3.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_7_3
