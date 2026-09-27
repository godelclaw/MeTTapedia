import Mettapedia.GraphTheory.FourColor.ExecutableJointTransfer
import Mettapedia.GraphTheory.FourColor.VertexCodeJoint

/-!
# Executable physical vertex-code evaluation

Only the three-dart star is enumerated. Old pieces are represented by
their finite boundary supports, permutations and cut records. The whole
run is proved equal to extraction from the constructed literal tangle.
The integer Euler coordinate is exact, not silently capped.
-/

namespace Mettapedia.GraphTheory.FourColor.ExecutableVertexCode

open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open VertexAttachmentTransfer ExecutableJointTransfer

variable {P R : Type*} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]

def starState (order : Fin 3 ≃ P ⊕ R) : State P R where
  colours := Finset.univ.filter fun xy =>
    (∀ b : P ⊕ R, Sum.elim xy.1 xy.2 b ≠ 0) ∧ Function.Injective (Sum.elim xy.1 xy.2)
  face := order.permCongr turn
  cuts := BoundarySmallCutExecutable.extractTangle (star order)
  mass := 4

theorem starState_exact (order : Fin 3 ≃ P ⊕ R) :
    denote (starState order) = SerialTangleJointTransfer.encode (star order) := by
  apply SerialTangleJointTransfer.Signature.ext
  · ext xy
    change xy ∈ Finset.univ.filter _ ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (star_accepts order xy.1 xy.2).symm
  · exact (star_face_code order).symm
  · exact BoundarySmallCutExecutable.extractTangle_correct (star order)
  · exact (star_mass order).symm

variable {l r : ℕ} (a : Code l r) (h : Valid a)

def step (s : State (Fin 0) (Fin l)) : State (Fin 0) (Fin r) :=
  transport (outCoordinates a)
    (transfer (transport (inCoordinates a h) s) (starState (starOrder a h)))

theorem step_exact (s : State (Fin 0) (Fin l)) :
    denote (step a h s) = VertexCodeJoint.step a h (denote s) := by
  unfold step VertexCodeJoint.step
  rw [transport_exact, transfer_exact, transport_exact, starState_exact]

def start (a : Code 0 r) (h : Valid a) : State (Fin 0) (Fin r) :=
  transport (initialCoordinates a) (starState (starOrder a h))

theorem start_exact (a : Code 0 r) (h : Valid a) :
    denote (start a h) = VertexCodeJoint.start a h := by
  unfold start VertexCodeJoint.start
  rw [transport_exact, starState_exact]

open VertexCodeTrace

def evaluate : {r : ℕ} → Trace r → State (Fin 0) (Fin r)
  | _, .first a h => start a h
  | _, .step t a h => step a h (evaluate t)

theorem evaluate_exact {r} (t : Trace r) :
    denote (evaluate t) = VertexCodeJoint.Trace.signature t := by
  induction t with
  | first a h => exact start_exact a h
  | step t a h ih =>
    change denote (step a h (evaluate t)) = _
    rw [step_exact, ih]
    rfl

open Classical in
/-- Reflection against the actual object, not only against another evaluator. -/
theorem evaluate_physical {r} (t : Trace r) :
    denote (evaluate t) = SerialTangleJointTransfer.encode t.realize := by
  classical
  rw [evaluate_exact, VertexCodeJoint.Trace.signature_exact]

def accepts (t : Trace 0) : Bool :=
  decide ((Fin.elim0, Fin.elim0) ∈ (evaluate t).colours)

theorem accepts_exact (t : Trace 0) :
    accepts t = true ↔ ∃ c, t.realize.IsTaitColoring c := by
  classical
  rw [accepts, decide_eq_true_eq]
  have hh := congrArg SerialTangleJointTransfer.Signature.colours (evaluate_physical t)
  have hm := Set.ext_iff.mp hh (Fin.elim0, Fin.elim0)
  change ((Fin.elim0, Fin.elim0) ∈ (evaluate t).colours ↔
    VertexCodeRealization.Supports t.realize Fin.elim0) at hm
  rw [hm, Trace.support_exact, ← Trace.closed_exact]

end Mettapedia.GraphTheory.FourColor.ExecutableVertexCode
