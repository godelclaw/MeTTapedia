import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement

/-!
# Facial returns stay in actual exterior components

Open facial steps either cross an interior edge or rotate at a fixed
vertex. Their powers, and hence their boundary returns, supply actual
paths in the interior multigraph. This observation turns boundary order
into component connectivity without assuming a connected exterior.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleFaceReturnConnectivity

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph OpenTangleMarkedFace
open OpenTanglePortReplacement SerialTangleFaceTransfer SerialTangleFaceCode
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24BoundaryFaceReturnProfile
open GoertzelV24SeamFaceArc

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I B : Type*} [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] (O : OpenTangleData V I B)

omit [Fintype I] [Fintype B] [DecidableEq B] in
theorem phi_reach (d : I ⊕ B) :
    (sideMultigraph O).Reach (O.vertOf d) (O.vertOf (openPhi O d)) := by
  have hv : O.vertOf (openPhi O d) =
      O.vertOf ((Equiv.sumCongr O.interiorAlpha (Equiv.refl B)) d) := O.vert_rho _
  rw [hv]
  cases d with
  | inr b => exact .refl
  | inl i =>
    exact Relation.ReflTransGen.single
      ⟨sideEdgeOf O i, not_false, sideMultigraph_ends O i⟩

omit [Fintype I] [Fintype B] [DecidableEq B] in
theorem pow_reach (d : I ⊕ B) (n : ℕ) :
    (sideMultigraph O).Reach (O.vertOf d) (O.vertOf ((openPhi O ^ n) d)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (phi_reach O _)

omit [DecidableEq B] in
theorem sameCycle_reach {d e : I ⊕ B} (h : (openPhi O).SameCycle d e) :
    (sideMultigraph O).Reach (O.vertOf d) (O.vertOf e) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact pow_reach O d n

/-- A computed boundary return joins ports in one actual interior component. -/
theorem return_reach (b : B) :
    (sideMultigraph O).Reach (O.boundaryVert b) (O.boundaryVert (returnCode O b)) := by
  let root : {d : I ⊕ B // Boundary d} := ⟨.inr b, trivial⟩
  have h := sameCycle_reach O (nextHit_sameCycle (openPhi O) Boundary root)
  have hc : (boundaryCoordinate I B).symm (returnCode O b) =
      nextHitPerm (openPhi O) Boundary root := by
    simp only [returnCode, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  have hv := congrArg (fun d : {d : I ⊕ B // Boundary d} => O.vertOf d.1) hc
  change O.boundaryVert (returnCode O b) =
    O.vertOf (nextHitPerm (openPhi O) Boundary root).1 at hv
  change (sideMultigraph O).Reach (O.boundaryVert b) _ at h
  rw [hv]
  exact h

end
end Mettapedia.GraphTheory.FourColor.OpenTangleFaceReturnConnectivity
