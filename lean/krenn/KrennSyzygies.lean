import Mathlib

namespace Krenn

variable {R : Type*} [CommRing R]

/-- The coefficient identity extracted from a sparse C6 cellular certificate. -/
theorem cofactor_transversal_syzygy (a b c u z : R) :
    a * b * z + (a * c + u) - a * (b * z + c) = u := by
  ring

/-- Three cofactor relations force the transversal term to vanish. -/
theorem transversal_eq_zero
    (a b c u z : R)
    (hz : z = 0)
    (hac : a * c + u = 0)
    (hbz : b * z + c = 0) :
    u = 0 := by
  calc
    u = a * b * z + (a * c + u) - a * (b * z + c) := by ring
    _ = 0 := by rw [hac, hbz, hz]; ring

/-- A live (in particular, unit) transversal contradicts those relations. -/
theorem no_common_zero_of_live_transversal
    [Nontrivial R]
    (a b c u z : R)
    (hu : IsUnit u)
    (hz : z = 0)
    (hac : a * c + u = 0)
    (hbz : b * z + c = 0) : False := by
  exact hu.ne_zero (transversal_eq_zero a b c u z hz hac hbz)

/-- Number of vertices carrying colour `c`. -/
def colourCount (ι : Fin 6 → Fin 3) (c : Fin 3) : Nat :=
  (Finset.univ.filter fun v => ι v = c).card

/- Three disjoint bichromatic edges induce exactly one of the balanced
profiles `(3,3)`, `(3,2,1)`, or `(2,2,2)` (zeros retain the unused colour in
the first profile).  This fixed finite lemma is the profile-adaptive
replacement for the false `(3,2,1)`-only claim. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem alternating_transversal_profile :
    ∀ ι : Fin 6 → Fin 3,
      ι 0 ≠ ι 1 → ι 2 ≠ ι 3 → ι 4 ≠ ι 5 →
      ([colourCount ι 0, colourCount ι 1, colourCount ι 2].Perm [0, 3, 3] ∨
       [colourCount ι 0, colourCount ι 1, colourCount ι 2].Perm [1, 2, 3] ∨
       [colourCount ι 0, colourCount ι 1, colourCount ι 2].Perm [2, 2, 2]) := by
  decide

end Krenn
