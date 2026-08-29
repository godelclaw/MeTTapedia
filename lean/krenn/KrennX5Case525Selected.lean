import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case525Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "90eb07a76800b3037f24ce010df2a1bbd0659cbc55c7a48dc7299136b8ca001d"
def sourceSystemSemanticSHA256 : String := "c90b6e0eda3fc9b9f515723cd854b8c2beadfe966b705fd905aa04eb9bbbdc9e"
def certificateSHA256 : String := "bb67d6854fb88bd36021c15c865ca0b20b20ec31b418be54f53d223cf967e145"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 675 := ![
  0,
  1,
  2,
  3,
  32,
  33,
  407,
  422,
  423,
  424,
  425,
  426,
  435,
  470,
  490,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1), (66, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (66, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (18, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(20, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (40, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (10, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (25, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (17, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (9, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (11, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (48, 1), (53, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (48, 1), (51, 1), (53, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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

#print axioms Krenn.X5Case525Selected.selectedHasNoCommonZero

end Krenn.X5Case525Selected
