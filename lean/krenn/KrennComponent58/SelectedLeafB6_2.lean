import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "99b1959ef43e22c53de4672a7ad892daea046936881fc4fb5b27fe0075ef3922"
def certificateSHA256 : String := "6998bde24f5dcf682abbfb522c779a88787cc9273df92e84a003b5c8d7fb1f42"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 619 := ![
  10,
  11,
  23,
  29,
  30,
  37,
  38,
  63,
  73,
  192,
  193,
  200,
  220,
  241,
  333,
  339,
  340,
  341,
  342,
  353,
  396,
  438,
  474,
  480,
  481,
  507,
  512,
  562,
  576,
  577,
  610,
  612,
  614,
  615,
  616,
  618
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(14, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(9, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (25, 1), (31, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (22, 1), (25, 1), (34, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (22, 1), (25, 1), (34, 1), (56, 1), (60, 1)] }, { coefficient := 2, powers := [(19, 1), (22, 1), (24, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (15, 1), (31, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (41, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (32, 1), (35, 1), (43, 1), (47, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 2), (50, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (48, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (18, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (29, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (32, 1), (35, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (34, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (20, 1), (25, 1), (34, 1), (54, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (34, 1), (56, 1), (60, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (15, 1), (29, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (29, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (35, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := -1, powers := [(14, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (28, 1), (50, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (28, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (31, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (25, 1), (28, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (32, 1), (35, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (25, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (25, 1), (56, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (31, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (34, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (15, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (31, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (32, 1), (35, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (20, 1), (25, 1), (34, 1), (52, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (34, 1), (52, 1), (56, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (37, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (46, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (31, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (31, 1), (32, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 2), (31, 1), (41, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (31, 1), (32, 1), (35, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_2.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_2
