import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase1293.Certificate

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "194887386d5ae71e6db92f70f5ca2d82cee670c4d31c304198edc7ded7d0df4d"
def sourceSystemSemanticSHA256 : String := "03385be05385390ed9962c27f060e50897c7ffbf55cbbb2ddbe63aefd8e113fd"
def certificateSHA256 : String := "809f0890a1ad03df288d5ef7ab8013ebc55b530c2e37607997e9aabadc1479f6"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 11 → Fin 675 := ![
  411,
  412,
  413,
  414,
  420,
  421,
  422,
  425,
  659,
  664,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(34, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (32, 1), (34, 1), (35, 1), (36, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (34, 1), (38, 1), (39, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (32, 1), (34, 1), (41, 1), (42, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(32, 2), (35, 1), (36, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 2), (38, 1), (39, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 2), (41, 1), (42, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (34, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (34, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (34, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (32, 1), (34, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (34, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(16, 1), (32, 1), (34, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (34, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (32, 1), (34, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (34, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (32, 1), (34, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(32, 2), (35, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 2), (38, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 2), (41, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (34, 1), (35, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (41, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase1293.Certificate.selectedHasNoCommonZero

end Krenn.X5ResidualCase1293.Certificate
