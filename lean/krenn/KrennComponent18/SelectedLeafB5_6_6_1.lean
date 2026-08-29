import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB5_6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "24dbc81db3705aa23541599d6298428c8ab4509cbce78a83dc60d8688533ca09"
def certificateSHA256 : String := "96e3763d9faecf50dcf7c07a76f43176745da23dc8d1a4b4ffb5874f3709a86f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 670 := ![
  10,
  11,
  17,
  19,
  142,
  167,
  294,
  295,
  301,
  318,
  323,
  409,
  433,
  437,
  443,
  584,
  657,
  658,
  663,
  664,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (26, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (31, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (40, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (45, 1), (54, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (20, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (20, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (52, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (54, 1), (61, 2)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (20, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (54, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (37, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (31, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (49, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (37, 1), (40, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (24, 1), (45, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (34, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := 2, powers := [(0, 1), (17, 1), (24, 1), (47, 1), (54, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (18, 1), (24, 1), (42, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (49, 1), (54, 1), (61, 2)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (45, 1), (52, 1), (54, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB5_6_6_1.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB5_6_6_1
