import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5baf8ec99bc7e63e10621812932ca977c3eea1bf12dc5616d2440516ff47417d"
def certificateSHA256 : String := "6c6d98ce1377a493db2fd03a7dc233595a63541b7203046a005eeeaa944c3060"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 671 := ![
  19,
  24,
  26,
  29,
  189,
  193,
  196,
  254,
  309,
  310,
  420,
  421,
  423,
  540,
  557,
  661,
  664,
  666,
  667,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(23, 1), (45, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (53, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (46, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (54, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (54, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (57, 2), (65, 1)] }, { coefficient := -2, powers := [(28, 1), (47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (49, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(40, 1), (55, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 2), (65, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(18, 1), (23, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (14, 1), (19, 1), (23, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (23, 1), (57, 2), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (28, 1), (47, 1), (57, 1), (65, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (54, 1), (57, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB6_2_5.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB6_2_5
