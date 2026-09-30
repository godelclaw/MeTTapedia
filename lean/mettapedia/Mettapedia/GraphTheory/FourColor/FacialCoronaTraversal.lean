import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces

/-!
# Following the neighbouring faces of a cubic facial cycle

The central face supplies a cyclic sequence of darts. Crossing its spokes
and following the adjacent faces constructs the next boundary. A face of
length `n + 3` supplies an `n`-step connection between consecutive spoke
endpoints. The same argument covers every central cycle length and every
neighbouring face length; no new boundary is supplied as input.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialCoronaTraversal

open Equiv Equiv.Perm PhysicalForkCodeFaces

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) {k : ℕ} [NeZero k] (center : Fin k → RS.D)

/-- Cross the third edge of a central vertex. -/
def incoming (i : Fin k) : RS.D := RS.alpha (RS.rho (center i))

/-- Start following the outside part of the neighbouring face. -/
def first (i : Fin k) : RS.D := RS.rho (incoming RS center i)

omit [NeZero k] in
theorem first_eq (i : Fin k) :
    first RS center i = (RS.phi ^ 2) (RS.alpha (center i)) := by
  simp [first, incoming, RotationSystem.phi, pow_two, Perm.mul_apply,
    RS.alpha_involutive]

theorem incoming_face (hC : Cubic3 RS)
    (hcenter : ∀ i, RS.phi (center i) = center (i + 1)) (i : Fin k) :
    RS.phi (incoming RS center (i + 1)) = RS.alpha (center i) := by
  rw [incoming, ← hcenter i]
  simp only [RotationSystem.phi, Perm.mul_apply, RS.alpha_involutive]
  exact hC.cube _

/-- The neighbouring face closes the new outer arc. -/
theorem outside_arc (hC : Cubic3 RS)
    (hcenter : ∀ i, RS.phi (center i) = center (i + 1))
    (n : ℕ) (i : Fin k)
    (hface : (RS.phi ^ (n + 3)) (RS.alpha (center i)) = RS.alpha (center i)) :
    (RS.phi ^ n) (first RS center i) = incoming RS center (i + 1) := by
  apply RS.phi.injective
  rw [incoming_face RS center hC hcenter i, first_eq]
  calc
    RS.phi ((RS.phi ^ n) ((RS.phi ^ 2) (RS.alpha (center i)))) =
        (RS.phi ^ (n + 3)) (RS.alpha (center i)) := by
      conv_rhs =>
        rw [show n + 3 = (n + 2) + 1 by omega, pow_succ', Perm.mul_apply,
          pow_add, Perm.mul_apply]
    _ = RS.alpha (center i) := hface

/-- In a cubic star the inverse facial step is another explicit dart word. -/
theorem eq_last_of_face_eq (hC : Cubic3 RS) {d e : RS.D}
    (h : RS.phi d = e) : d = RS.alpha (RS.rho (RS.rho e)) := by
  apply RS.phi.injective
  rw [h]
  simp only [RotationSystem.phi, Perm.mul_apply, RS.alpha_involutive, hC.cube]

/-- A pentagonal neighbour contributes two edges between spoke endpoints. -/
theorem pentagonal_last (hC : Cubic3 RS)
    (hcenter : ∀ i, RS.phi (center i) = center (i + 1)) (i : Fin k)
    (hface : (RS.phi ^ 5) (RS.alpha (center i)) = RS.alpha (center i)) :
    RS.phi (first RS center i) =
      RS.alpha (RS.rho (RS.rho (incoming RS center (i + 1)))) := by
  apply eq_last_of_face_eq RS hC
  exact outside_arc RS center hC hcenter 2 i hface

/-- A hexagonal neighbour contributes three edges between spoke endpoints. -/
theorem hexagonal_last (hC : Cubic3 RS)
    (hcenter : ∀ i, RS.phi (center i) = center (i + 1)) (i : Fin k)
    (hface : (RS.phi ^ 6) (RS.alpha (center i)) = RS.alpha (center i)) :
    RS.phi (RS.phi (first RS center i)) =
      RS.alpha (RS.rho (RS.rho (incoming RS center (i + 1)))) := by
  apply eq_last_of_face_eq RS hC
  exact outside_arc RS center hC hcenter 3 i hface

end Mettapedia.GraphTheory.FourColor.FacialCoronaTraversal
