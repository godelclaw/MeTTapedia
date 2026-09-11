import Mettapedia.GraphTheory.FourColor.ExecutableVertexCode

/-!
# The face/Euler projection of executable vertex attachment

The topology update depends only on the old face permutation and mass,
not on colour supports or cut records. Mass is translated additively.
These facts permit controls for accumulation of closed components without
enumerating their growing interiors.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeGeometry

open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open ExecutableJointTransfer ExecutableVertexCode

variable {l r : ℕ} (a : Code l r) (h : Valid a)

def zeroAt (p : Equiv.Perm (Fin 0 ⊕ Fin l)) : State (Fin 0) (Fin l) :=
  ⟨∅, p, ∅, 0⟩

def faceStep (p : Equiv.Perm (Fin 0 ⊕ Fin l)) : Equiv.Perm (Fin 0 ⊕ Fin r) :=
  (step a h (zeroAt p)).face

def massDelta (p : Equiv.Perm (Fin 0 ⊕ Fin l)) : ℤ :=
  (step a h (zeroAt p)).mass

theorem step_face (s : State (Fin 0) (Fin l)) :
    (step a h s).face = faceStep a h s.face := rfl

theorem step_mass (s : State (Fin 0) (Fin l)) :
    (step a h s).mass = s.mass + massDelta a h s.face := by
  simp only [step, massDelta, zeroAt, transport, transfer]
  ring

end Mettapedia.GraphTheory.FourColor.VertexCodeGeometry
