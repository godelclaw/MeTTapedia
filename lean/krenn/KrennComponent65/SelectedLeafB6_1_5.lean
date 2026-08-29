import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d0101bf2ace11d8b2ce32033ce3ab763fbd1c7ac40f2f17b3a91d689875c38e9"
def certificateSHA256 : String := "247d89026d4b384d7d0e0e5491c73d039611789cd8eabc90b4989cf40c703a2e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 671 := ![
  12,
  15,
  19,
  24,
  26,
  29,
  254,
  278,
  309,
  310,
  315,
  414,
  420,
  421,
  423,
  434,
  540,
  582,
  645,
  661,
  662,
  664,
  666,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 2), (31, 1), (36, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (31, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (34, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (40, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (34, 1), (40, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (45, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (45, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (28, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (13, 1), (36, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (13, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (18, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (18, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 2), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (23, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (23, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (40, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (28, 1), (40, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (51, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (51, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (28, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (28, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (51, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (13, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (42, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (36, 1), (37, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (40, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (36, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (44, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (37, 1), (59, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (40, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (44, 1), (47, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (47, 1), (54, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (18, 1), (23, 1), (24, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (24, 1), (28, 1), (36, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (24, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (18, 1), (23, 1), (24, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (24, 1), (28, 1), (40, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (18, 1), (24, 1), (28, 1), (40, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 3), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 2), (13, 1), (19, 1), (23, 1), (36, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 2), (13, 1), (19, 1), (28, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (44, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (23, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (44, 1), (47, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (19, 1), (28, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (44, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (25, 1), (42, 1), (51, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (51, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_1_5.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_1_5
