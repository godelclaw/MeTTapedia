import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case526Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0fd0f888f3f2430470060a1a5269508e0bbd328dcb5762bd3e73bdee68640c1e"
def sourceSystemSemanticSHA256 : String := "38dd3ff2d7eb944119bbaa6e3e48dbcefd96437ea86605d9bf553c93ed644971"
def certificateSHA256 : String := "4bf99fdc83fe54de946db7f33a0ca197e592c7586d658f83584134dba1d35c6a"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 675 := ![
  0,
  26,
  30,
  32,
  46,
  47,
  48,
  49,
  54,
  55,
  417,
  420,
  423,
  424,
  425,
  426,
  427,
  492,
  629,
  661,
  664,
  668,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (39, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (42, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (42, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (42, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (43, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (42, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (33, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (23, 1), (33, 1), (36, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (31, 1)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (26, 1), (31, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (26, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (25, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (31, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (26, 1), (31, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (39, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (33, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (33, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (26, 1), (31, 1), (49, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (28, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(28, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(11, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (31, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (33, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (43, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (33, 1), (36, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case526Selected.selectedHasNoCommonZero

end Krenn.X5Case526Selected
