import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "69cb80dde3dce0042127cbd7cdb4d3395aa5f400236a8c37a2fcf1fb20fcedcb"
def certificateSHA256 : String := "28fbdace46a84b08e923ccf41033e9ade44b8e578d8925b22fa217865e5639f6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 19 → Fin 616 := ![
  4,
  10,
  39,
  210,
  227,
  228,
  233,
  334,
  342,
  353,
  362,
  466,
  474,
  490,
  571,
  612,
  613,
  614,
  615
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(8, 1), (25, 1), (31, 1), (46, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (35, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (45, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (40, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(14, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (35, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (39, 1), (40, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (2, 1), (43, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (35, 1), (45, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (28, 1), (35, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (25, 1), (31, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (35, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1)] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB3.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB3
