import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_6_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bc22157d68b0ee65df15a2355d926daed9ade72703e592e891f52cdbec5391c8"
def certificateSHA256 : String := "eb544981ff2b19f4af32ab32cef92d1b96880b39d247745aca4cdff17d9d8ce6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  10,
  19,
  142,
  162,
  167,
  168,
  294,
  295,
  301,
  318,
  323,
  403,
  409,
  433,
  437,
  443,
  562,
  584,
  657,
  658,
  663,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (31, 1), (52, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (31, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (54, 1), (61, 2)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (31, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (31, 1), (45, 1), (52, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (45, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(13, 1), (31, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (45, 1), (54, 1), (56, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (42, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_6_2_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_6_2_1
