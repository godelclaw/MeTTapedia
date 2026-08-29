import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case269Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e99888fbe028fe37e9718c9afc3afeade5aaeebdb30dd0918f5d114b223df965"
def sourceSystemSemanticSHA256 : String := "804e9888c1f25130e313828624b421e94aa77f19986a87616b0d4f2434bda943"
def certificateSHA256 : String := "e5c82db99448775d69af621f5d9a2f58b440465e2239ffa0bcdc674b8cf2af81"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 7 → Fin 675 := ![
  2,
  3,
  415,
  420,
  424,
  667,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (24, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (10, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (24, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
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
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case269Selected.selectedHasNoCommonZero

end Krenn.X5Case269Selected
