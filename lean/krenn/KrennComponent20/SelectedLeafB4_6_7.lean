import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e3299de9bc84eb5155469d74a303d35c54632b642f9691c5cd50326334723846"
def certificateSHA256 : String := "d382b6bc4119dbfe617b69847041e85d45315c623949d5191c38754d229858ae"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 50 → Fin 645 := ![
  15,
  23,
  107,
  133,
  144,
  146,
  163,
  165,
  179,
  183,
  184,
  185,
  186,
  190,
  191,
  193,
  196,
  199,
  284,
  285,
  288,
  344,
  345,
  346,
  347,
  352,
  353,
  362,
  388,
  415,
  440,
  462,
  466,
  470,
  473,
  480,
  485,
  490,
  506,
  511,
  551,
  557,
  558,
  635,
  636,
  638,
  640,
  641,
  642,
  643
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (21, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (24, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 50 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(21, 1), (29, 1), (45, 1)] }, { coefficient := 2, powers := [(24, 1), (25, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (26, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (56, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (24, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (29, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (24, 1), (56, 1)] }, { coefficient := -2, powers := [(24, 1), (25, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(25, 1), (29, 1), (40, 1), (47, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(21, 1), (29, 1), (43, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (26, 1), (43, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (26, 1), (43, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := 2, powers := [(24, 1), (40, 1), (49, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(24, 1), (43, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := -2, powers := [(24, 1), (43, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }, { coefficient := -2, powers := [(29, 1), (40, 1), (47, 1), (49, 1), (60, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (24, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(21, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (56, 1)] }, { coefficient := 2, powers := [(13, 1), (14, 1), (56, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (40, 1), (56, 1), (64, 1)] }, { coefficient := -2, powers := [(24, 1), (56, 1)] }, { coefficient := -2, powers := [(29, 1), (40, 1), (47, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (24, 1), (51, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (45, 1), (49, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (49, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (49, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (53, 1), (55, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (29, 1), (45, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (21, 1), (29, 1), (43, 1), (51, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (40, 1), (56, 1), (60, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (29, 1), (40, 1), (47, 1), (60, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(24, 1), (43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -2, powers := [(18, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (29, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(18, 1), (21, 1), (29, 1), (43, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (45, 1), (49, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (26, 1), (43, 1), (49, 1), (51, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (40, 1), (49, 1), (56, 1), (64, 1)] }, { coefficient := 2, powers := [(18, 1), (24, 1), (43, 1), (49, 1), (52, 1)] }, { coefficient := -2, powers := [(18, 1), (24, 1), (43, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (40, 1), (47, 1), (49, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (47, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := -1, powers := [(41, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (56, 1)] }, { coefficient := -2, powers := [(46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (24, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (18, 1), (29, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (19, 1), (29, 1), (55, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -2, powers := [(17, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(18, 1), (28, 1), (56, 1)] }, { coefficient := 2, powers := [(18, 1), (29, 1), (43, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (14, 1), (24, 1), (56, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (24, 1), (25, 1), (40, 1), (56, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := -2, powers := [(13, 1), (25, 1), (29, 1), (40, 1), (47, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 50,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_6_7.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_6_7
