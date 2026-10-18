import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-! Cofactor elimination for a transversal monomial. -/

namespace Mettapedia.Algebra.Polynomial.Certificate.Transversal

variable {R : Type*} [CommRing R]

/-- A polynomial combination eliminating the two cofactor variables. -/
theorem cofactor_identity (a b c u z : R) :
    a * b * z + (a * c + u) - a * (b * z + c) = u := by
  ring

/-- Three cofactor relations force the transversal term to vanish. -/
theorem eq_zero_of_cofactor_relations (a b c u z : R)
    (hz : z = 0) (hac : a * c + u = 0) (hbz : b * z + c = 0) :
    u = 0 := by
  calc
    u = a * b * z + (a * c + u) - a * (b * z + c) :=
      (cofactor_identity a b c u z).symm
    _ = 0 := by rw [hac, hbz, hz]; ring

/-- A unit transversal rules out a common zero of these cofactor relations. -/
theorem not_cofactor_relations_of_isUnit [Nontrivial R] (a b c u z : R)
    (hu : IsUnit u) (hz : z = 0) (hac : a * c + u = 0)
    (hbz : b * z + c = 0) : False :=
  hu.ne_zero (eq_zero_of_cofactor_relations a b c u z hz hac hbz)

end Mettapedia.Algebra.Polynomial.Certificate.Transversal
