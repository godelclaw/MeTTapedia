import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b12f5a6fe931e255886ba866431dccdcd2fcc39323cb45fa780330f340594b27"
def certificateSHA256 : String := "1e481900360dedd4801376689eca6e64200fd30c867fb1b4a6c6a2a149b2681f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 545 := ![
  31,
  35,
  41,
  48,
  69,
  77,
  89,
  143,
  151,
  152,
  166,
  168,
  285,
  403,
  404,
  406,
  415,
  433,
  508,
  536,
  537,
  539,
  540,
  541,
  542,
  543,
  544
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (47, 1)] }, { coefficient := 1, powers := [(10, 1), (60, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (47, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1), (34, 1), (47, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (37, 1), (47, 1)] }, { coefficient := 1, powers := [(31, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (60, 1)] }, { coefficient := 1, powers := [(32, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (58, 1)] }, { coefficient := 1, powers := [(43, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (48, 1)] }, { coefficient := 1, powers := [(40, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (48, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(1, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(27, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (45, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (4, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (47, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(6, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (12, 1), (32, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (34, 1), (47, 1), (48, 1)] }, { coefficient := 2, powers := [(0, 1), (19, 1), (37, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (22, 1), (47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (47, 1), (58, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (12, 1), (53, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (20, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (27, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (7, 1), (47, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (4, 1), (28, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (4, 1), (33, 1)] }, { coefficient := 2, powers := [(2, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (37, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (32, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (32, 1), (47, 1)] }, { coefficient := -2, powers := [(0, 1), (32, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (37, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (28, 1), (47, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (33, 1), (47, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (3, 1), (4, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (47, 1)] }, { coefficient := 2, powers := [(1, 1), (2, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (55, 1)] }, { coefficient := 2, powers := [(2, 1), (19, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1)] }, { coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(1, 1), (2, 1), (3, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (7, 1), (45, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (7, 1), (47, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (10, 1), (47, 1), (48, 1), (58, 1), (60, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3B0NW15NonzeroCertificate
