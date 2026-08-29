import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB5_6_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "286088df9300773df4c4035415d3fcfca776005eacda401f9a1ad069ab8f9f60"
def certificateSHA256 : String := "0fadfcea617d09cc62ae6c1d915ca335f7c58539587ff4b43b6f4fa156dea1ed"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 29 → Fin 591 := ![
  1,
  2,
  5,
  25,
  36,
  47,
  48,
  56,
  224,
  276,
  366,
  367,
  370,
  384,
  385,
  388,
  389,
  410,
  503,
  507,
  559,
  579,
  581,
  582,
  584,
  585,
  587,
  588,
  590
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 62) := ![
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (20, 1), (30, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (20, 1), (23, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (18, 1), (31, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (18, 1), (24, 1), (39, 1), (48, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (40, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (37, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (31, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (39, 1), (48, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (24, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (6, 1), (20, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (39, 1), (48, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (6, 1), (20, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (31, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (39, 1), (43, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (39, 1), (40, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (31, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(2, 1), (9, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(2, 1), (20, 1), (39, 1), (48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1)] }]
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
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB5_6_2.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB5_6_2
