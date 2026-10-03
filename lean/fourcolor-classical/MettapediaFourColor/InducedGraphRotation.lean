import MettapediaFourColor.GraphRotationRows
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction

/-! # Actual induced graph rotations by first return

Deleting vertices retains exactly the darts with both endpoints outside the
deleted set. First return of the ambient vertex rotation supplies the cyclic
order on the actual induced graph. Planarity and face geometry are separate.
-/

namespace FourColor.InducedGraphRotation

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24SeamFaceArc
open PermutationFirstReturnRestriction

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (keep : Set V)

def retained (d : G.Dart) : Prop := d.fst ∈ keep ∧ d.snd ∈ keep

def darts : (G.induce keep).Dart ≃ {d : G.Dart // retained keep d} where
  toFun d := ⟨⟨(d.fst.val, d.snd.val), d.adj⟩, d.fst.property, d.snd.property⟩
  invFun d := ⟨(⟨d.val.fst,d.property.1⟩, ⟨d.val.snd,d.property.2⟩), d.val.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem pow_fst (data : Data G) (n : ℕ) (d : G.Dart) :
    ((data.vertexRotation ^ n) d).fst = d.fst := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, data.vertexRotation_fst, ih]

def rotation (data : Data G) (outer : (G.induce keep).Dart) : Data (G.induce keep) where
  vertexRotation := (darts keep).symm.permCongr (nextHitPerm data.vertexRotation (retained keep))
  vertexRotation_fst d := by
    apply Subtype.ext
    exact pow_fst data _ _
  outer := outer

theorem cyclic (data : Data G) (hc : data.IsVertexwiseCyclic)
    (outer : (G.induce keep).Dart) : (rotation keep data outer).IsVertexwiseCyclic := by
  intro v
  let r := rotation keep data outer
  refine ⟨⟨?_, r.vertexRotation.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (r.vertexRotation_fst d).trans hd
  · intro d hd
    refine ⟨r.vertexRotation.symm d, ?_, r.vertexRotation.apply_symm_apply d⟩
    have h := r.vertexRotation_fst (r.vertexRotation.symm d)
    rw [r.vertexRotation.apply_symm_apply] at h
    exact h.symm.trans hd
  · intro a ha b hb
    have h : data.vertexRotation.SameCycle (darts keep a).val (darts keep b).val :=
      (hc v.val).2 (congrArg Subtype.val ha) (congrArg Subtype.val hb)
    have hn := (nextHitPerm_sameCycle_iff data.vertexRotation (retained keep)
      (darts keep a) (darts keep b)).mpr h
    exact (permCongr_sameCycle_iff (darts keep).symm _ _ _).mpr hn

/-- A prescribed finite arc supplies the exact first retained successor. -/
theorem next_of_arc (data : Data G) (outer : (G.induce keep).Dart)
    (a b : (G.induce keep).Dart) {n : ℕ}
    (arc : ReturnArc data.vertexRotation (retained keep)
      (darts keep a).val (darts keep b).val n) :
    (rotation keep data outer).vertexRotation a = b := by
  have h := nextHit_eq_of_returnArc data.vertexRotation (retained keep)
    (darts keep a) (darts keep b) arc
  exact congrArg (darts keep).symm h

end
end FourColor.InducedGraphRotation
