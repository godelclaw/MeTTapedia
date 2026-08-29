import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case819Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "32507ed5a71f48100f865c9a8a7d09d5436ce27a46247eec74645d296cd55599"
def sourceSystemSemanticSHA256 : String := "104a099a2321dbfb4369e697656aedf0f0a52001933e5fa52c4ed6c6c613e2d1"
def certificateSHA256 : String := "bad2f017e302f9733380ab61bd8f484a3f637ea3cd4ed53c929e494ab0a75041"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 675 := ![
  0,
  1,
  2,
  3,
  24,
  25,
  393,
  416,
  419,
  422,
  423,
  424,
  425,
  427,
  439,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(29, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (42, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (40, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (37, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (26, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (26, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (26, 1), (34, 1), (37, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (43, 1), (62, 1)] }, { coefficient := 1, powers := [(29, 1), (34, 1), (37, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (18, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (34, 1), (37, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (40, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (34, 1), (37, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (48, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case819Selected.selectedHasNoCommonZero

end Krenn.X5Case819Selected
