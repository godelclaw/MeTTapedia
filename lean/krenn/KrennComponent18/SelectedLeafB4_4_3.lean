import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component18.SelectedLeafB4_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5717e70bdfe047da8db2842f66b0e75f7c8c426a42a712e64d285032c68b186b"
def certificateSHA256 : String := "333fc5aedb5d841da5a9ef463b3e1b4224f51d167f68c671d815fb47b0940116"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 667 := ![
  7,
  9,
  10,
  19,
  142,
  156,
  159,
  162,
  163,
  167,
  168,
  171,
  295,
  301,
  315,
  318,
  319,
  409,
  433,
  437,
  443,
  562,
  564,
  591,
  609,
  657,
  658,
  660,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (53, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (45, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(30, 1), (49, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (46, 1), (49, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(31, 1), (49, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(20, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (46, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (24, 1), (53, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (26, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (49, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (47, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (47, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (47, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (45, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (24, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(13, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(30, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(31, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(31, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1), (48, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (49, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -2, powers := [(5, 1), (31, 1), (56, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (24, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (45, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (49, 1), (63, 1)] }, { coefficient := 2, powers := [(18, 1), (19, 1), (24, 1), (54, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (25, 1), (54, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (30, 1), (53, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (31, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (18, 1), (31, 1), (56, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (37, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (30, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component18.SelectedLeafB4_4_3.selectedHasNoCommonZero

end Krenn.Component18.SelectedLeafB4_4_3
