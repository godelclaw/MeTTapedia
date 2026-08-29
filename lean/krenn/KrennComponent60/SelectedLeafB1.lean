import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7f39ee1f54b3f6e7b028a3a9600691da6bd815ce2facdf4dfa0d1f203cf0e388"
def certificateSHA256 : String := "b0790a3b7cb8957ec4ec16e6cbabd2e0035d42118c545b0175c2fb2a71ca366a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 659 := ![
  1,
  2,
  4,
  22,
  25,
  143,
  145,
  172,
  178,
  184,
  293,
  295,
  314,
  315,
  316,
  358,
  367,
  433,
  435,
  442,
  443,
  448,
  459,
  460,
  467,
  556,
  579,
  608,
  609,
  621,
  643,
  655,
  656,
  658
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(2, 1), (26, 1), (41, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (20, 1), (35, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (21, 1), (35, 1), (50, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (35, 1), (47, 1), (50, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (26, 1), (41, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (32, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (38, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (25, 1), (32, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (36, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (36, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (36, 1), (47, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (21, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (36, 1), (47, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (36, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (18, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (18, 1), (20, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (20, 1), (38, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (29, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (35, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (35, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (54, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (29, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (25, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(29, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(24, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (24, 1), (26, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (21, 1), (35, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (41, 1), (43, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (43, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (29, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (20, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (25, 1), (29, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(18, 1), (29, 1), (36, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (41, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (3, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (36, 1), (56, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (26, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(2, 2), (36, 1), (38, 1), (56, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 2), (36, 1), (47, 1), (53, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (26, 1), (37, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (26, 1), (40, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (26, 1), (45, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (18, 1), (24, 1), (45, 1), (53, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (18, 1), (29, 1), (47, 1), (51, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (18, 1), (20, 1), (29, 1), (36, 1), (47, 1), (51, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (25, 1), (29, 1), (36, 1), (47, 1), (51, 1), (56, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (40, 1), (41, 1), (57, 1)] }, { coefficient := 2, powers := [(2, 1), (41, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(2, 1), (41, 1), (46, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (43, 1), (45, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (32, 1), (46, 1), (53, 1)] }, { coefficient := 2, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (52, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (41, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (45, 1), (47, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (35, 1), (47, 1), (52, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (40, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (36, 1), (45, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (36, 1), (45, 1), (53, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (36, 1), (47, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (3, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (38, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (20, 1), (38, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (25, 1), (48, 1), (51, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (26, 1), (41, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(2, 1), (26, 1), (41, 1), (46, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (35, 1), (45, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (32, 1), (43, 1), (45, 1)] }, { coefficient := 2, powers := [(5, 1), (26, 1), (32, 1), (46, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (21, 1), (35, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (32, 1), (48, 1), (51, 1)] }, { coefficient := -2, powers := [(8, 1), (25, 1), (35, 1), (45, 1), (47, 1), (50, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB1
