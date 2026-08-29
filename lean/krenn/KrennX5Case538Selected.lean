import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case538Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "6327a7cdd892a13363b44563ab3b649522e4427679fee87be7c0f566fbc666f1"
def sourceSystemSemanticSHA256 : String := "ba3dbfe3d981a75f2b3397d83ac0d86c987f9724b382608dc9e93e67ee6e95a1"
def certificateSHA256 : String := "72cf1cc699076688323dac738eed451588c5ea2c6525d8e64660566fab5293d5"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 675 := ![
  1,
  27,
  31,
  42,
  43,
  45,
  47,
  48,
  49,
  50,
  51,
  390,
  398,
  415,
  425,
  426,
  427,
  428,
  513,
  528,
  661,
  662,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (49, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (49, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (48, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (36, 1), (49, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (42, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (36, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (39, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (36, 1), (49, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (36, 1), (43, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (42, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (42, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (19, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (18, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (19, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (19, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (11, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (19, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (19, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (34, 1), (39, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(20, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case538Selected.selectedHasNoCommonZero

end Krenn.X5Case538Selected
