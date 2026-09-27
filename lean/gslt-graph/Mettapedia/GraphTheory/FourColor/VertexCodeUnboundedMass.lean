import Mettapedia.GraphTheory.FourColor.VertexCodeGeometry
import Mettapedia.GraphTheory.FourColor.VertexCodeChecks

/-!
# Exact Euler mass is not finite on all bounded-width code runs

Disjoint planar two-vertex, three-edge components can accumulate while
the frontier never exceeds three. Their exact Euler masses are distinct.
This refutes finiteness of the unrestricted exact-mass carrier, not of
the viable-prefix quotient: these completed components cannot be joined
by any later vertex. It does not refute a connected counterexample route.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeUnboundedMass

open VertexCodeTrace VertexCodeChecks VertexCodeGeometry ExecutableVertexCode
open ExecutableJointTransfer

set_option Elab.async false
set_option maxRecDepth 16000

def Within (b : ℕ) : {r : ℕ} → Trace r → Prop
  | r, .first _ _ => r ≤ b
  | r, .step t _ _ => Within b t ∧ r ≤ b

def addComponent (t : Trace 0) : Trace 0 :=
  .step (.step t birth birth_valid) (close true) (close_valid true)

theorem empty_face_unique (p : Equiv.Perm (Fin 0 ⊕ Fin 0)) : p = Equiv.refl _ :=
  Subsingleton.elim _ _

theorem component_delta :
    massDelta birth birth_valid (Equiv.refl _) +
      massDelta (close true) (close_valid true)
        (faceStep birth birth_valid (Equiv.refl _)) = 4 := by
  simp only [massDelta, faceStep, zeroAt]
  decide +kernel

theorem addComponent_mass (t : Trace 0) :
    (evaluate (addComponent t)).mass = (evaluate t).mass + 4 := by
  change (step (close true) (close_valid true)
    (step birth birth_valid (evaluate t))).mass = _
  rw [step_mass, step_mass, step_face, empty_face_unique (evaluate t).face]
  have hh := component_delta
  omega

def family : ℕ → Trace 0
  | 0 => twoStars true
  | n + 1 => addComponent (family n)

theorem family_width (n : ℕ) : Within 3 (family n) := by
  induction n with
  | zero => exact ⟨show 3 ≤ 3 from le_rfl, show 0 ≤ 3 from Nat.zero_le _⟩
  | succ n ih => exact ⟨⟨ih, by decide⟩, by decide⟩

theorem family_mass (n : ℕ) : (evaluate (family n)).mass = 4 * (n + 1 : ℤ) := by
  induction n with
  | zero => exact flat_mass
  | succ n ih =>
    change (evaluate (addComponent (family n))).mass = _
    rw [addComponent_mass, ih]
    push_cast
    ring

theorem unbounded_mass (bound : ℕ) :
    ∃ t : Trace 0, Within 3 t ∧ (bound : ℤ) < (evaluate t).mass := by
  refine ⟨family bound, family_width bound, ?_⟩
  rw [family_mass]
  omega

theorem distinct_profiles : Function.Injective (fun n => evaluate (family n)) := by
  intro m n h
  have hh := congrArg State.mass h
  rw [family_mass, family_mass] at hh
  omega

end Mettapedia.GraphTheory.FourColor.VertexCodeUnboundedMass
