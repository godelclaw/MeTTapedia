import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case608Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e067bd47df85a0986d446aa31a6b4e61459df48168afb12745ac9f91a6584b0c"
def sourceSystemSemanticSHA256 : String := "35d101eb5f0dd003873241681eeebf1619f86027dd4fddc7a09c0c17f3ae69e3"
def certificateSHA256 : String := "3e1accf7972b9a6950a322fc8b07c50d2ceb01e3aecec69e6ce721fbf10eb870"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 675 := ![
  0,
  27,
  31,
  41,
  42,
  44,
  46,
  49,
  50,
  51,
  52,
  391,
  398,
  416,
  424,
  425,
  426,
  427,
  512,
  527,
  660,
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
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (40, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(40, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (48, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (48, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (48, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (26, 1), (47, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (26, 1), (36, 1), (48, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (26, 1), (42, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (36, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (28, 1), (39, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (36, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (43, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (36, 1), (43, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (42, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (36, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (42, 1), (50, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (34, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (40, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (34, 1), (37, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (18, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (11, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (23, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(23, 1), (28, 1), (34, 1), (39, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(21, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }]
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

#print axioms Krenn.X5Case608Selected.selectedHasNoCommonZero

end Krenn.X5Case608Selected
