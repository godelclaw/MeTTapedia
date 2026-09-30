import Mettapedia.GraphTheory.FourColor.DualTruncateFaceGeometry
import Mettapedia.GraphTheory.FourColor.VertexCodeCyclicEncoder
import Mathlib.Logic.Equiv.Sum

/-!
# Cyclic frames selected by an actual face cover

A face-only vertex cover chooses exactly one facial corner at each target
vertex. The next dart fixes slot zero; the marked corner is slot two.
The existing cyclic-star encoder supplies the complete dart equivalence.
This is the framing step of inverse leapfrog recognition, following the
face-cover interpretation of Fowler and Pisanski (1994),
https://doi.org/10.1039/FT9949002865.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateFaceCoverFrame

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open VertexCodeCyclicEncoder

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {W F : Type u} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  (T : RotationSystem.{u,u,u} W F)

/-- The cover refers to actual quotient faces, and counts facial corners.
It retains a unique marked dart at each vertex, not just a face-length label. -/
structure Cover where
  marked : OrbitFace T → Prop
  unique : ∀ v : W, ∃! d : T.D, T.vertOf d = v ∧ marked (dartOrbitFace T d)

/-- All darts are enumerated in their actual vertex rotation. -/
structure Frame where
  dart : W × Fin 3 ≃ T.D
  vertex : ∀ x, T.vertOf (dart x) = x.1
  turn : ∀ x, T.rho (dart x) = dart (x.1, x.2 + 1)

def star (hc : T.IsCubic) (hcyc : VertexRotationCyclic T)
    (root : ∀ v, At T v) (v : W) : Fin 3 ≃ At T v :=
  (cyclicStarEquiv (RS := T) (inner := fun _ => False)
    hc not_false hcyc (root v)).trans
      (newDartEquiv (RS := T) (inner := fun _ => False) not_false)

def frame (hc : T.IsCubic) (hcyc : VertexRotationCyclic T)
    (root : ∀ v, At T v) : Frame T where
  dart := ((Equiv.sigmaEquivProd W (Fin 3)).symm.trans
    (Equiv.sigmaCongrRight (star T hc hcyc root))).trans (Equiv.sigmaFiberEquiv T.vertOf)
  vertex x := (cyc (root x.1) x.2).2
  turn x := by
    change T.rho ((cyc (root x.1) x.2).1) = (cyc (root x.1) (x.2 + 1)).1
    exact cyclicStarEquiv_succ (RS := T) (inner := fun _ => False)
      hc not_false hcyc (root x.1) x.2

def markedDart (c : Cover T) (v : W) : At T v :=
  ⟨(c.unique v).exists.choose, (c.unique v).exists.choose_spec.1⟩

theorem markedDart_marked (c : Cover T) (v : W) :
    c.marked (dartOrbitFace T (markedDart T c v).1) :=
  (c.unique v).exists.choose_spec.2

theorem markedDart_unique (c : Cover T) (v : W) (d : At T v)
    (h : c.marked (dartOrbitFace T d.1)) : d = markedDart T c v := by
  apply Subtype.ext
  exact (c.unique v).unique ⟨d.2, h⟩
    ⟨(markedDart T c v).2, markedDart_marked T c v⟩

def fromCover (hc : T.IsCubic) (hcyc : VertexRotationCyclic T)
    (c : Cover T) : Frame T :=
  frame T hc hcyc (fun v => rot (markedDart T c v))

/-- The observed cover fixes the marked corner to slot two exactly. -/
theorem fromCover_marked_iff (hc : T.IsCubic) (hcyc : VertexRotationCyclic T)
    (c : Cover T) (x : W × Fin 3) :
    c.marked (dartOrbitFace T ((fromCover T hc hcyc c).dart x)) ↔ x.2 = 2 := by
  rcases x with ⟨v, i⟩
  change c.marked (dartOrbitFace T ((cyc (rot (markedDart T c v)) i).1)) ↔ i = 2
  have h0 := rot_ne hc hcyc (markedDart T c v)
  have h1 := rot_ne_two hc hcyc (markedDart T c v)
  have h2 := rot_three hc hcyc (markedDart T c v)
  fin_cases i
  · simp only [cyc, Function.iterate_zero_apply]
    constructor
    · intro h
      exact (h0 (markedDart_unique T c v _ h)).elim
    · exact fun h => ((by decide : (0 : Fin 3) ≠ 2) h).elim
  · simp only [cyc, Function.iterate_one]
    constructor
    · intro h
      exact (h1 (markedDart_unique T c v _ h)).elim
    · exact fun h => ((by decide : (1 : Fin 3) ≠ 2) h).elim
  · change c.marked (dartOrbitFace T ((rot (rot (rot (markedDart T c v)))).1)) ↔
      (2 : Fin 3) = 2
    rw [h2]
    exact iff_of_true (markedDart_marked T c v) rfl

end
end Mettapedia.GraphTheory.FourColor.DualTruncateFaceCoverFrame
