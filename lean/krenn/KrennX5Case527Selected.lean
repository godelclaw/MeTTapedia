import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case527Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "5b1ef77ecdd11690737be49ef1939d85ae340d25635af48c9b4780376b8240a9"
def sourceSystemSemanticSHA256 : String := "b73707e0e86b225304dea3ef7018941d90c467366022ea1baafe0005db66be29"
def certificateSHA256 : String := "86f2128237ccaaf3256b86bfdd07c5ae08f3b984ecc5355c3b4480f2d2d58d04"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  1,
  2,
  3,
  32,
  33,
  405,
  416,
  419,
  422,
  423,
  424,
  425,
  426,
  435,
  496,
  661,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (39, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (39, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (20, 1), (25, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (33, 1), (36, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(33, 1), (34, 1), (36, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (25, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (34, 1), (43, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (40, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (33, 1), (37, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(28, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := -1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case527Selected.selectedHasNoCommonZero

end Krenn.X5Case527Selected
