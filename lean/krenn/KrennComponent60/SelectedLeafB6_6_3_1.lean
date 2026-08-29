import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_6_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d765e91c7989165cf6467db383460ca7f00899cf8fdc5f448a4e346bbd71676d"
def certificateSHA256 : String := "4717dcc5c332c62069f326dc308cefb14cb125abb9cea1c20743344bf3d0c617"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 17 → Fin 668 := ![
  150,
  151,
  153,
  211,
  292,
  304,
  312,
  422,
  463,
  582,
  583,
  608,
  659,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(40, 1), (43, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1), (63, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (40, 1), (57, 1), (63, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(40, 1), (63, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (45, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (51, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (40, 1), (43, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (45, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (56, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (26, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (40, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (40, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (40, 1), (63, 1)] }, { coefficient := 1, powers := [(9, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (43, 1), (45, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (26, 1), (40, 1), (43, 1), (51, 1), (56, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (40, 1), (43, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (26, 1), (46, 1), (51, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (43, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (46, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (9, 1), (40, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (40, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (40, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (40, 1), (57, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(9, 1), (40, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (40, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (63, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_6_3_1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_6_3_1
