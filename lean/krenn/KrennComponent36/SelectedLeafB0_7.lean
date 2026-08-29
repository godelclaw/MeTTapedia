import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB0_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cd833cd2b8496e5fabb1be32f904eecea2ad66025d7067e0cfe1cd31f995fc8a"
def certificateSHA256 : String := "379750d1a8a4c2689d7627516a00937dd69e7b34b6210845e14ecd816c1f2cc2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 669 := ![
  10,
  14,
  15,
  18,
  19,
  271,
  299,
  301,
  305,
  307,
  320,
  322,
  325,
  441,
  448,
  451,
  457,
  470,
  473,
  480,
  483,
  595,
  613,
  647,
  651,
  652,
  662,
  663,
  665,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(45, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (32, 1), (40, 1), (46, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (32, 1), (40, 1), (47, 1), (48, 1), (52, 1), (64, 1)] }, { coefficient := -4, powers := [(20, 1), (29, 1), (40, 1), (45, 1), (48, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(29, 1), (40, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(32, 1), (38, 1), (40, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (23, 1), (40, 1), (46, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(23, 1), (40, 1), (41, 1), (43, 1), (64, 1)] }, { coefficient := -2, powers := [(23, 1), (40, 1), (48, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (32, 1), (40, 1), (41, 1), (47, 1), (51, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (28, 1), (40, 1), (41, 1), (50, 1), (51, 1), (54, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (40, 1), (41, 1), (50, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (32, 1), (40, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (40, 1), (50, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(23, 1), (40, 1), (50, 1), (55, 1), (64, 1)] }, { coefficient := -2, powers := [(32, 1), (38, 1), (40, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (25, 1), (32, 1), (40, 1), (41, 1), (47, 1), (62, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (28, 1), (40, 1), (41, 1), (50, 1), (54, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (29, 1), (40, 1), (41, 1), (50, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (45, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (13, 1), (25, 1), (32, 1), (40, 1), (47, 1), (52, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (29, 1), (40, 1), (41, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (32, 1), (38, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (32, 1), (40, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (40, 1), (50, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (40, 1), (48, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (20, 1), (32, 1), (40, 1), (55, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (48, 1), (64, 1)] }, { coefficient := 4, powers := [(13, 1), (20, 1), (29, 1), (40, 1), (48, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (13, 1), (25, 1), (32, 1), (40, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (46, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (25, 1), (32, 1), (40, 1), (47, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (29, 1), (40, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (23, 1), (40, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (40, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (40, 1), (43, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (40, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(40, 1), (50, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (40, 1), (41, 1), (50, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (43, 1), (64, 1)] }, { coefficient := 2, powers := [(40, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (40, 1), (50, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (40, 1), (64, 1)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (40, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (40, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (19, 1), (32, 1), (40, 1), (48, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (37, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (40, 1), (43, 1), (45, 1), (53, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (25, 1), (32, 1), (40, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (32, 1), (40, 1), (43, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (41, 1), (43, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (43, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (32, 1), (40, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (38, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (40, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := -4, powers := [(13, 1), (20, 1), (29, 1), (40, 1), (45, 1), (48, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (38, 1), (40, 1), (61, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (40, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (23, 1), (40, 1), (48, 1), (55, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (40, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(13, 1), (32, 1), (38, 1), (40, 1), (48, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (37, 1), (40, 1), (50, 1), (60, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (40, 2), (50, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (40, 1), (45, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (40, 1), (45, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(40, 1), (41, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(40, 1), (47, 1), (50, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(40, 1), (47, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (38, 1), (40, 1), (50, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (40, 2), (41, 1), (50, 1), (58, 1), (63, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (40, 1), (41, 1), (46, 1), (50, 1), (54, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (40, 1), (41, 1), (50, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(20, 1), (40, 1), (48, 1), (50, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (18, 1), (25, 1), (32, 1), (40, 1), (41, 1), (47, 1), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (28, 1), (40, 1), (41, 1), (50, 1), (54, 1), (63, 1), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (20, 1), (29, 1), (40, 1), (41, 1), (50, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (20, 1), (35, 1), (40, 1), (41, 1), (50, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (29, 1), (40, 1), (41, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (40, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(41, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB0_7.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB0_7
