import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "76bd8d8f4c963629788a3505e0bc2c3f09051a999b8af58f2771bb91e7370242"
def certificateSHA256 : String := "00e29018870243656c83c3a654837f1c35299af348547952daeea5cfc6c8d528"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 620 := ![
  7,
  10,
  16,
  20,
  26,
  29,
  35,
  192,
  205,
  299,
  337,
  349,
  363,
  408,
  471,
  567,
  576,
  578,
  579,
  609,
  610,
  611,
  612,
  613,
  614,
  616,
  619
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(7, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (34, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (24, 1), (26, 1), (49, 1), (56, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (26, 1), (56, 1), (57, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (26, 1), (28, 1), (42, 1), (57, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(31, 1), (34, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (24, 1), (49, 2), (61, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (34, 1), (61, 1)] }, { coefficient := -1, powers := [(20, 1), (37, 1), (44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (24, 1), (49, 1), (51, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (25, 1), (51, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (28, 1), (42, 1), (51, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (24, 1), (44, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (25, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (28, 1), (42, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (24, 1), (49, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (25, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (28, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (24, 1), (49, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (25, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (28, 1), (42, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 2), (61, 1)] }, { coefficient := -2, powers := [(25, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(25, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(31, 1), (34, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (49, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (24, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (24, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (24, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (24, 1), (49, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (22, 1), (25, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (28, 1), (42, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (56, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(37, 1), (44, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(37, 1), (53, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (35, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (25, 1), (38, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (35, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (38, 1), (42, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (24, 1), (26, 1), (49, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (25, 1), (26, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (26, 1), (28, 1), (42, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1), (49, 2)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (31, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (9, 1), (24, 1), (26, 1), (49, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (9, 1), (25, 1), (26, 1), (56, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (9, 1), (26, 1), (28, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (22, 1), (24, 1), (49, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (18, 1), (22, 1), (25, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (18, 1), (22, 1), (28, 1), (42, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (31, 1), (34, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (49, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB4_7_3.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_7_3
