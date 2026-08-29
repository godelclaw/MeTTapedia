import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component12.SelectedLeafB0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a39fb94a65a35e760f3ddf407c17ac3e1a18e6ee36548ff5cf29e73c39317b57"
def certificateSHA256 : String := "bf88fc500da8c76909be08621a4eb5cc26ac3f322a41ea9bf5c0a2d55c8ce30f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 616 := ![
  8,
  12,
  16,
  17,
  20,
  22,
  23,
  27,
  35,
  209,
  213,
  216,
  218,
  292,
  333,
  339,
  340,
  349,
  350,
  399,
  458,
  464,
  473,
  476,
  479,
  491,
  549,
  561,
  562,
  580,
  582,
  605,
  612,
  613,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (50, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(5, 2), (23, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (28, 1), (54, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(5, 2), (18, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (54, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (31, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (28, 1), (31, 1), (42, 1), (47, 1), (54, 2)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (47, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (47, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (22, 1), (24, 1), (31, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (34, 1), (37, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (22, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (22, 1), (24, 2), (31, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (23, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (28, 1), (31, 1), (40, 1), (42, 1), (54, 2)] }, { coefficient := -1, powers := [(28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (17, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (8, 1), (24, 1), (31, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 2), (24, 1), (31, 1), (34, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (17, 1), (22, 1), (24, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (28, 1), (31, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(22, 1), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (18, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (24, 1), (31, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (17, 1), (24, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2)] }, { coefficient := 1, powers := [(28, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (22, 1), (24, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 2), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (42, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (22, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 2), (24, 1), (28, 1), (31, 1), (35, 1), (42, 1), (54, 2), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 2), (24, 1), (28, 1), (31, 1), (42, 1), (54, 2), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (24, 1), (31, 1), (34, 1), (42, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (8, 1), (24, 1), (31, 1), (34, 1), (40, 1), (42, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (22, 1), (24, 1), (31, 1), (42, 1), (44, 1), (52, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (24, 1), (28, 1), (31, 1), (40, 1), (42, 1), (54, 2)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (39, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (42, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (31, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (35, 1), (54, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (42, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (45, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (39, 1), (54, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (44, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (31, 1), (37, 1), (42, 1), (54, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (47, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := 1, powers := [(40, 1), (55, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component12.SelectedLeafB0.selectedHasNoCommonZero

end Krenn.Component12.SelectedLeafB0
