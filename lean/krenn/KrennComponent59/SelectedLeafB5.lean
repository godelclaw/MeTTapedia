import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fb522cd402d295b82eb036b1cf99444344c8c6049bf314cba4ea3404335c4403"
def certificateSHA256 : String := "f238aaec627d850236a38528a01f1f98f1dcb765e893f42262fae576269153c7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 614 := ![
  1,
  4,
  5,
  6,
  7,
  9,
  16,
  20,
  29,
  34,
  35,
  37,
  40,
  192,
  203,
  222,
  224,
  235,
  247,
  251,
  299,
  332,
  337,
  349,
  358,
  363,
  396,
  444,
  471,
  493,
  497,
  558,
  567,
  579,
  609,
  610,
  611,
  612,
  613
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (44, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (28, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (25, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (25, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (25, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (29, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (18, 1), (22, 1), (51, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (20, 1), (44, 1), (47, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (29, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (44, 1), (54, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (31, 1), (34, 1), (38, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (31, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (44, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (7, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (31, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (47, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (4, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (14, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (29, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (31, 1), (37, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (29, 1), (31, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (42, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (34, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (43, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (42, 1), (49, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (4, 1), (20, 1), (44, 1), (47, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (20, 1), (44, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (4, 1), (31, 1), (38, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (28, 1), (38, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (25, 1), (38, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (25, 1), (38, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (29, 1), (31, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (28, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (25, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (25, 1), (29, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (29, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (33, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (22, 1), (42, 1), (51, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB5.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB5
