import Mettapedia.GraphTheory.FourColor.VertexCodeTrace
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint

/-!
# One finite code updates all coordinates of the same constructed tangle

The semantic operation takes only a boundary signature and a valid finite
code. Its physical correctness is inherited from attachment and exact
boundary transport. This is not yet an optimized executable reflection of
the signature, whose sets and permutations here are semantic objects.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeJoint

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open VertexAttachmentTransfer TwoSidedBoundaryJoint SerialTangleJointTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

variable {l r : ℕ} (a : Code l r) (h : Valid a)

def step (s : Signature (Fin 0) (Fin l)) : Signature (Fin 0) (Fin r) :=
  transport (outCoordinates a)
    (transfer (transport (inCoordinates a h) s) (encode (star (starOrder a h))))

theorem step_exact {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I]
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)) :
    encode (attach a h T) = step a h (encode T) := by
  unfold attach step
  rw [joint_reindex, joint_append]
  unfold prepared
  rw [joint_reindex]

def start (a : Code 0 r) (h : Valid a) : Signature (Fin 0) (Fin r) :=
  transport (initialCoordinates a) (encode (star (starOrder a h)))

theorem start_exact (a : Code 0 r) (h : Valid a) :
    encode (initial a h) = start a h := joint_reindex _ _

theorem encode_decEq {V I : Type*} [Fintype V] [Fintype I]
    (T : TwoSidedOpenTangleData V I (Fin 0) (Fin r)) (d e : DecidableEq I) :
    @encode V I (Fin 0) (Fin r) _ _ d _ _ _ _ T =
      @encode V I (Fin 0) (Fin r) _ _ e _ _ _ _ T := by
  cases Subsingleton.elim d e
  rfl

namespace Trace

open VertexCodeTrace

def signature : {r : ℕ} → Trace r → Signature (Fin 0) (Fin r)
  | _, .first a h => start a h
  | _, .step t a h => step a h (signature t)

theorem signature_exact {r} (t : Trace r) :
    encode t.realize = signature t := by
  induction t with
  | first a h =>
    exact (encode_decEq (initial a h) _ _).trans (start_exact a h)
  | step t a h ih =>
    letI : DecidableEq t.Interior := Classical.decEq _
    exact (encode_decEq (attach a h t.realize) _ _).trans
      ((step_exact a h t.realize).trans (congrArg (step a h) ih))

end Trace
end
end Mettapedia.GraphTheory.FourColor.VertexCodeJoint
