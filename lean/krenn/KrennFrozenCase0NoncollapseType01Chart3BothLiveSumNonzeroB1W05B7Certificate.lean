import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B7Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "883674777e9a52924f18426960176e228fd21b3a57247c33179443e790787fdd"
def certificateSHA256 : String := "6aa8d0001042f06339911f72daf98fec28f7399104f0c7c5a8fc081e39e30649"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 689 := ![
  71,
  133,
  187,
  197,
  214,
  215,
  217,
  313,
  322,
  330,
  336,
  495,
  507,
  568,
  586,
  650,
  671,
  672,
  678,
  679,
  680,
  681,
  682,
  684,
  687,
  688
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 78) := ![
  [{ coefficient := 1, powers := [(25, 1), (32, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (65, 1)] }, { coefficient := 1, powers := [(44, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(48, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (71, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(30, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (72, 1)] }, { coefficient := 1, powers := [(23, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (71, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (65, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (72, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(33, 1)] }],
  [{ coefficient := 1, powers := [(34, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (76, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (77, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 78) := ![
  [{ coefficient := 1, powers := [(9, 1), (69, 1), (76, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1), (76, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (11, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (11, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (22, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (22, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (68, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (72, 1)] }],
  [{ coefficient := 2, powers := [(15, 1), (72, 1), (76, 1)] }, { coefficient := 1, powers := [(23, 1), (69, 1), (76, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (57, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (50, 1), (68, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (12, 1), (36, 1), (72, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (45, 1), (69, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (50, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (9, 1), (50, 1), (68, 1), (72, 1), (77, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (47, 1), (50, 1), (72, 1), (77, 1)] }],
  [{ coefficient := -1, powers := [(37, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (65, 1), (68, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (68, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(9, 1), (11, 1), (47, 1), (50, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (11, 1), (47, 1), (50, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (47, 1), (50, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (47, 1), (50, 1), (68, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (45, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (42, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (27, 1), (36, 1), (65, 1), (72, 1), (73, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (50, 1), (57, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (14, 1), (50, 1), (68, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (19, 1), (50, 1), (57, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (50, 1), (68, 2), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (27, 1), (50, 1), (57, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(9, 1), (27, 1), (50, 1), (62, 1), (68, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (11, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(1, 1), (11, 1), (22, 1), (45, 1), (69, 1), (73, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (9, 1), (11, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (11, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (9, 1), (14, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (15, 1), (62, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (15, 1), (68, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (11, 1), (22, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (11, 1), (22, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (62, 1), (71, 1), (72, 1)] }, { coefficient := -1, powers := [(6, 1), (9, 1), (14, 1), (15, 1), (68, 1), (71, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (62, 1), (65, 1), (72, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (14, 1), (22, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (11, 1), (65, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (65, 1), (68, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (45, 1), (57, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (36, 1), (65, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (25, 1), (32, 1), (69, 1), (76, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (32, 1), (48, 1), (76, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (53, 1), (69, 1)] }, { coefficient := -2, powers := [(15, 1), (37, 1), (72, 1)] }, { coefficient := -1, powers := [(15, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(23, 1), (37, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (9, 1), (50, 1), (52, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(8, 1), (9, 1), (50, 1), (62, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (47, 1), (50, 1), (52, 1), (72, 1)] }, { coefficient := -1, powers := [(9, 1), (14, 1), (47, 1), (50, 1), (62, 1), (72, 1)] }]
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
    (values : Fin 78 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B7Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1W05B7Certificate
