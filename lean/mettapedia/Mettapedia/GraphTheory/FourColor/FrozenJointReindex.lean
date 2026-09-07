import Mettapedia.GraphTheory.FourColor.FrozenPhysicalCount

/-! # Joint supports in a common finite boundary coordinate system

Reindexing a seam changes its word coordinates but leaves each observation
of an input dart unchanged. Thus equality in the finite standard-coordinate
carrier implies equality at the physical matching used by replacement.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenJointReindex

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge GoertzelV24OpenTangleComposition
open FrozenCountSupport FrozenPhysicalCount

universe u v
variable {W J R L K : Type u} {M : Type v}

def joint (right : OpenTangleData W J R) (matching : L ≃ R)
    (obs : M → Option (J ⊕ R)) :=
  innerJointSupport (rightClosedPortTangle right matching)
    (fun m => (obs m).map (rightPortDart matching))

def reindexDart (e : L ≃ K) : J ⊕ (L ⊕ EmptyPort.{u}) ≃ J ⊕ (K ⊕ EmptyPort.{u}) :=
  Equiv.sumCongr (Equiv.refl J) (Equiv.sumCongr e (Equiv.refl _))

def pullColoring (right : OpenTangleData W J R) (matching : K ≃ R) (e : L ≃ K)
    (c : Coloring (rightClosedPortTangle right matching)) :
    Coloring (rightClosedPortTangle right (e.trans matching)) where
  color d := c.color (reindexDart e d)
  invariant d := c.invariant d

theorem pullColoring_proper (right : OpenTangleData W J R) (matching : K ≃ R)
    (e : L ≃ K) (c : Coloring (rightClosedPortTangle right matching))
    (hc : IsProper c) : IsProper (pullColoring right matching e c) := by
  refine ⟨fun d => hc.1 _, ?_⟩
  intro d d' hv hn
  apply hc.2 _ _ ?_ (fun he => hn ((reindexDart e).injective he))
  have hvert : ∀ d, (rightClosedPortTangle right matching).vert (reindexDart e d) =
      (rightClosedPortTangle right (e.trans matching)).vert d := by
    rintro (d | (d | d)) <;> rfl
  exact (hvert d).trans (hv.trans (hvert d').symm)

theorem mem_joint_pull (right : OpenTangleData W J R) (matching : K ≃ R)
    (e : L ≃ K) (obs : M → Option (J ⊕ R)) (word : K → Color) (value : M → Color)
    (h : (word, value) ∈ joint right matching obs) :
    (word ∘ e, value) ∈ joint right (e.trans matching) obs := by
  obtain ⟨c, hc⟩ := h
  let c' : Col (rightClosedPortTangle right (e.trans matching))
      (Sum.elim (word ∘ e) PEmpty.elim) :=
    ⟨pullColoring right matching e c.val, pullColoring_proper _ _ _ _ c.property.1,
      funext (fun p => by
        rcases p with p | p
        · exact congrFun c.property.2 (Sum.inl (e p))
        · exact PEmpty.elim p)⟩
  refine ⟨c', ?_⟩
  rw [observes_map_iff] at hc ⊢
  intro m d hd
  have hr := hc m d hd
  change c.val.color (reindexDart e (rightPortDart (e.trans matching) d)) = value m
  have he : reindexDart e (rightPortDart (e.trans matching) d) = rightPortDart matching d := by
    cases d <;> simp [reindexDart, rightPortDart]
  rw [he]
  exact hr

theorem mem_joint_reindex_iff (right : OpenTangleData W J R) (matching : K ≃ R)
    (e : L ≃ K) (obs : M → Option (J ⊕ R)) (word : L → Color) (value : M → Color) :
    (word, value) ∈ joint right (e.trans matching) obs ↔
      (word ∘ e.symm, value) ∈ joint right matching obs := by
  constructor
  · intro h
    have hp := mem_joint_pull right (e.trans matching) e.symm obs word value h
    have he : e.symm.trans (e.trans matching) = matching := by ext p; simp
    simpa only [he] using hp
  · intro h
    have hp := mem_joint_pull right matching e obs (word ∘ e.symm) value h
    have he : (word ∘ e.symm) ∘ e = word := by funext p; simp
    simpa only [he] using hp

theorem joint_eq_of_coordinate_eq
    {W' J' R' : Type u}
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (oc : R ≃ K) (nc : R' ≃ K) (outside : L ≃ K)
    (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (h : joint old oc.symm oo = joint new nc.symm no) :
    joint old (outside.trans oc.symm) oo = joint new (outside.trans nc.symm) no := by
  ext p
  rcases p with ⟨word, value⟩
  rw [mem_joint_reindex_iff, mem_joint_reindex_iff, h]

end Mettapedia.GraphTheory.FourColor.FrozenJointReindex
