import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "247abd8dfc74ae121ed26adefa6f4fd9c17e4271fefcccc3d1891c962a2f57cc"
def certificateSHA256 : String := "e0171f45482f60c106e9b4881852fb54c704bdbdec041529d038a788aab41f89"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 620 := ![
  5,
  13,
  17,
  25,
  132,
  186,
  279,
  281,
  288,
  294,
  303,
  343,
  429,
  430,
  469,
  477,
  478,
  496,
  519,
  522,
  556,
  611,
  619
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (61, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(9, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (25, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(7, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (51, 1)] }, { coefficient := -1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (30, 1), (46, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (38, 1), (61, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (46, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (38, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (38, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (41, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (38, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (30, 1), (46, 1), (56, 1), (64, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B4W01NonzeroCertificate
