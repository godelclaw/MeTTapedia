import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB5_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a97dc594457281bd0ed3935569af709f50f9fafed0bb7994065d60065af9047d"
def certificateSHA256 : String := "62d73aa17f9c74599e449e04025a5e4ae026479937549499a943de1624dc08c3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 642 := ![
  9,
  16,
  27,
  33,
  97,
  165,
  179,
  185,
  186,
  192,
  193,
  194,
  196,
  199,
  284,
  291,
  315,
  317,
  346,
  347,
  348,
  350,
  352,
  353,
  364,
  367,
  457,
  462,
  466,
  484,
  499,
  527,
  534,
  551,
  557,
  580,
  634,
  635,
  637,
  638,
  640,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(43, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (26, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(13, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(4, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (37, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (35, 1), (41, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (35, 1), (41, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (27, 1), (35, 1), (41, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (37, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (11, 1), (18, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (35, 1), (41, 1), (46, 1), (58, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(20, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(23, 1), (26, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (41, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (18, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (18, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (25, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (20, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (32, 1), (52, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (32, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (25, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (26, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (47, 1), (53, 1), (55, 2), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (46, 1), (47, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (47, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (47, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (38, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (47, 1), (53, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (38, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (49, 1), (53, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (49, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (11, 1), (35, 1), (41, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (11, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (47, 1), (49, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (37, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (45, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (38, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (38, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (38, 1), (43, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (41, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (25, 1), (47, 1), (49, 1), (53, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (32, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (32, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (27, 1), (35, 1), (41, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (26, 1), (43, 1)] }, { coefficient := -1, powers := [(19, 1), (21, 1), (28, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (25, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (47, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (8, 1), (27, 1), (35, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (22, 1), (35, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (27, 1), (35, 1), (41, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (16, 1), (34, 1), (35, 1), (37, 1), (41, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB5_1.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB5_1
