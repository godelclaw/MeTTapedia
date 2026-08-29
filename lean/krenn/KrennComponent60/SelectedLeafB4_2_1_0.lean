import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_2_1_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c7a6bf5bbc2a5542b939e5d7570dea5ecc1b1203cca4b041adf99007ca316428"
def certificateSHA256 : String := "1194c0c24327e8c4aacbfc76e71143b55d411c07eeb7f2258d230fad8cbfca87"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 668 := ![
  6,
  8,
  14,
  22,
  154,
  301,
  302,
  305,
  377,
  378,
  404,
  431,
  443,
  497,
  500,
  525,
  537,
  556,
  605,
  654,
  655,
  657,
  658,
  661,
  663,
  664,
  665,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (48, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (23, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (31, 1), (45, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (34, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (23, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (31, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (34, 1), (46, 1), (51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (26, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (31, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (26, 1), (51, 2), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (31, 1), (37, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (34, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (24, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (24, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (31, 1), (45, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (34, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (59, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (48, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (31, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (38, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (34, 1), (40, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (34, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (34, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (34, 1), (35, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (20, 1), (24, 1), (34, 1), (46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (24, 1), (34, 1), (46, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (19, 1), (24, 1), (34, 1), (40, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (23, 1), (24, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (24, 1), (31, 1), (45, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (24, 1), (34, 1), (40, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (23, 1), (24, 1), (40, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (31, 1), (40, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (24, 1), (34, 1), (40, 2), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (24, 1), (34, 1), (46, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (26, 1), (46, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (46, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (31, 1), (37, 1), (46, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (37, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(15, 1), (31, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (26, 1), (40, 1), (51, 2), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (40, 1), (51, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (31, 1), (37, 1), (40, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (40, 1), (53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (34, 1), (48, 1), (51, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (34, 1), (47, 1), (50, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (31, 1), (45, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (34, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (11, 1), (34, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (23, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (31, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (34, 1), (40, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (23, 1), (47, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (31, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (34, 1), (40, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_2_1_0.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_2_1_0
