import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component10.SelectedLeafB5_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a6e7873a137edcdee8bf775da4ec1a054f66b0ee4be60578c1d3bd28f08ece0c"
def certificateSHA256 : String := "54f03218faa778dc37165abe9efcbf25ca58af7ece27fcd663d949e39a50974a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 40 → Fin 644 := ![
  5,
  8,
  19,
  24,
  35,
  162,
  163,
  164,
  167,
  169,
  170,
  181,
  189,
  190,
  202,
  284,
  349,
  350,
  359,
  363,
  369,
  442,
  460,
  462,
  463,
  464,
  465,
  466,
  471,
  490,
  550,
  557,
  568,
  595,
  634,
  635,
  638,
  640,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 40 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (48, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (48, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (27, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (43, 1), (45, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (38, 1), (43, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (23, 1), (43, 1), (58, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (23, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (43, 1), (55, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (18, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (23, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (36, 1), (52, 1), (59, 1)] }, { coefficient := 2, powers := [(29, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (36, 1), (47, 1), (59, 1)] }, { coefficient := 2, powers := [(23, 1), (36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (51, 1)] }, { coefficient := -2, powers := [(3, 1), (19, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (51, 1)] }, { coefficient := -1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (38, 1), (45, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (38, 1), (51, 1), (59, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (58, 1), (59, 1), (60, 1), (65, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := -2, powers := [(8, 1), (23, 1), (55, 1), (59, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (52, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (47, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(36, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(3, 1), (8, 1), (23, 1), (58, 1), (59, 1)] }, { coefficient := 2, powers := [(3, 1), (12, 1), (23, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (19, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (38, 1), (51, 1), (59, 1)] }, { coefficient := -2, powers := [(3, 1), (8, 1), (19, 1), (23, 1), (58, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(8, 1), (19, 1), (23, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(9, 1), (12, 1), (29, 1), (48, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 40,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component10.SelectedLeafB5_6_3.selectedHasNoCommonZero

end Krenn.Component10.SelectedLeafB5_6_3
