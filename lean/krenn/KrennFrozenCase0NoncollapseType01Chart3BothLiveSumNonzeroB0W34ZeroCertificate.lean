import KrennSparseCertificate

/-!
A selected-row reflection of the strict frozen B0 `w_34_11 = 0`
certificate.  The bridge module supplies the semantic route from these rows to
the canonical case-0 system and the displayed B0/chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9dea99aa89f4ef2b39f331dadc9299095a17f79a5716d773b41bfb07670381c0"
def certificateSHA256 : String := "fae28e1441232f76f3b7f7510c5900a6920ee164236284127165384d518ea427"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 693 := ![
  68, 133, 313, 331, 340, 494, 503, 506, 512, 515, 533, 577, 586, 632,
  650, 680, 686, 689, 690, 691, 692
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 76) := ![
  [{ coefficient := 1, powers := [(7, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (32, 1), (65, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (68, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (74, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (71, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (52, 1), (71, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (72, 1)] }, { coefficient := 1, powers := [(30, 1), (39, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (75, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (72, 1)] }, { coefficient := 1, powers := [(30, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (75, 1)] }, { coefficient := 1, powers := [(23, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1), (71, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (52, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (72, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (61, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (75, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (75, 1)] }, { coefficient := 1, powers := [(15, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 76) := ![
  [{ coefficient := 1, powers := [(9, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (11, 1), (71, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (52, 1), (75, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (48, 1), (71, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (48, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (50, 1), (52, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (50, 1), (57, 1), (75, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (57, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (57, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (50, 1), (71, 1), (75, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (50, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (50, 1), (75, 1)] }, { coefficient := -1, powers := [(12, 1), (45, 1), (72, 1)] }, { coefficient := -1, powers := [(12, 1), (48, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(32, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(37, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (38, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (42, 1), (66, 1)] }, { coefficient := -1, powers := [(37, 1), (38, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(38, 1), (45, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1), (52, 1), (72, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1), (52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1), (72, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (53, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (53, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (14, 1), (50, 1), (52, 1), (74, 1), (75, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (50, 1), (57, 1), (74, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (50, 1), (52, 1), (71, 1), (75, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (50, 1), (57, 1), (71, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (50, 1), (52, 1), (65, 1), (75, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (57, 1), (65, 1), (75, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (45, 1), (57, 1), (72, 1), (74, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (48, 1), (57, 1), (69, 1), (74, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (45, 1), (57, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(12, 1), (19, 1), (48, 1), (57, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (45, 1), (57, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (48, 1), (57, 1), (65, 1), (69, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (48, 1), (50, 1), (52, 1), (74, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (48, 1), (50, 1), (57, 1), (74, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (48, 1), (50, 1), (52, 1), (71, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (48, 1), (50, 1), (57, 1), (71, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (48, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (48, 1), (50, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (45, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (48, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (45, 1), (52, 1), (72, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (48, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (68, 1), (71, 1), (75, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (52, 1), (68, 1), (75, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (45, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (45, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (48, 1), (65, 1), (69, 1)] }, { coefficient := -1, powers := [(11, 1), (22, 1), (48, 1), (69, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (48, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (45, 1), (52, 1), (72, 1)] }, { coefficient := -1, powers := [(14, 1), (22, 1), (48, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (48, 1), (52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (52, 1), (71, 1), (75, 1)] }, { coefficient := 1, powers := [(9, 1), (50, 1), (57, 1), (71, 1), (75, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (52, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (52, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1), (52, 1), (71, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1), (57, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (36, 1), (38, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (36, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (61, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (15, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (9, 1), (50, 1), (52, 1), (75, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (48, 1), (50, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (47, 1), (50, 1), (75, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (32, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (47, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (45, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (38, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (38, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (45, 1), (50, 1)] }]
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
    (values : Fin 76 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB0W34ZeroCertificate
