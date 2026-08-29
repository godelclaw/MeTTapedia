import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component55.SelectedLeafB6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a34cd0c18b94253960f266dd7b94a98a96ccbd14c4e6ed24e9b3ff56c8a42ca1"
def certificateSHA256 : String := "8a4437ab915afb66d2a5e1b3e8584657761b9e11ad9e41a623249966c1807b98"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 590 := ![
  29,
  75,
  223,
  224,
  227,
  233,
  234,
  257,
  333,
  341,
  342,
  360,
  361,
  362,
  390,
  469,
  480,
  489,
  490,
  542,
  583,
  586,
  588,
  589
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(24, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (40, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (32, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 2), (29, 1), (57, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 2), (32, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 2), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 2), (25, 1), (29, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 2), (25, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 2), (25, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (29, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (8, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (26, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (8, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (6, 1), (29, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (29, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (29, 2), (57, 2)] }, { coefficient := -1, powers := [(5, 2), (29, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 2), (29, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (29, 1), (38, 1), (56, 1), (57, 2)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (32, 1), (38, 1), (54, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (35, 1), (38, 1), (51, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (38, 1), (57, 2)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (46, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (38, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 2), (29, 2), (57, 2)] }, { coefficient := -3, powers := [(0, 1), (5, 2), (29, 1), (32, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 2), (29, 1), (35, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (26, 1), (32, 1), (45, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (29, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (8, 1), (29, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (29, 1), (53, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component55.SelectedLeafB6_0.selectedHasNoCommonZero

end Krenn.Component55.SelectedLeafB6_0
