import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-! # Tait colourings with prescribed colours on named darts

Exact dart/vertex relabellings preserve the prescription pointwise. This
refines the colourability-only reassembly theorem; no condition is weakened
to ordinary non-colourability.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenDartTransport

open GoertzelV24VertexSideReassembly

universe uV uE vV vE m
variable {V : Type uV} {E : Type uE} {W : Type vV} {F : Type vE} {M : Type m}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- A named-dart prescription on the ordinary physical edge-colouring type. -/
def Accepts (RS : RotationSystem V E) (mark : M → RS.D) (value : M → Color) : Prop :=
  ∃ c : RS.EdgeColoring Color, RS.IsTaitEdgeColoring c ∧
    ∀ m, c (RS.edgeOf (mark m)) = value m

theorem accepts_of_dartEquiv (source : RotationSystem V E) (target : RotationSystem W F)
    (e : source.D ≃ target.D) (f : V ≃ W)
    (ha : ∀ d, e (source.alpha d) = target.alpha (e d))
    (hv : ∀ d, f (source.vertOf d) = target.vertOf (e d))
    (mark : M → source.D) (value : M → Color) (h : Accepts source mark value) :
    Accepts target (fun m => e (mark m)) value := by
  obtain ⟨c, hc, hm⟩ := h
  obtain ⟨c', hc', hread⟩ := exists_taitColoring_of_dartEquiv source target e f ha hv c hc
  exact ⟨c', hc', fun m => (hread (mark m)).trans (hm m)⟩

theorem accepts_iff_of_dartEquiv (source : RotationSystem V E) (target : RotationSystem W F)
    (e : source.D ≃ target.D) (f : V ≃ W)
    (ha : ∀ d, e (source.alpha d) = target.alpha (e d))
    (hv : ∀ d, f (source.vertOf d) = target.vertOf (e d))
    (mark : M → source.D) (value : M → Color) :
    Accepts source mark value ↔ Accepts target (fun m => e (mark m)) value := by
  constructor
  · exact accepts_of_dartEquiv source target e f ha hv mark value
  · intro h
    have ha' : ∀ d, e.symm (target.alpha d) = source.alpha (e.symm d) := by
      intro d
      apply e.injective
      rw [Equiv.apply_symm_apply, ha, Equiv.apply_symm_apply]
    have hv' : ∀ d, f.symm (target.vertOf d) = source.vertOf (e.symm d) := by
      intro d
      apply f.injective
      rw [Equiv.apply_symm_apply, hv, Equiv.apply_symm_apply]
    simpa only [Equiv.symm_apply_apply] using
      accepts_of_dartEquiv target source e.symm f.symm ha' hv' (fun m => e (mark m)) value h

/-- Reading all source representatives of an ambient name is the same
prescription after an exact dart relabelling. -/
theorem accepts_iff_named (source : RotationSystem V E) (target : RotationSystem W F)
    (e : source.D ≃ target.D) (f : V ≃ W)
    (ha : ∀ d, e (source.alpha d) = target.alpha (e d))
    (hv : ∀ d, f (source.vertOf d) = target.vertOf (e d))
    (mark : M → target.D) (value : M → Color) :
    (∃ c : source.EdgeColoring Color, source.IsTaitEdgeColoring c ∧
      ∀ m d, e d = mark m → c (source.edgeOf d) = value m) ↔ Accepts target mark value := by
  have h := accepts_iff_of_dartEquiv source target e f ha hv (fun m => e.symm (mark m)) value
  simp only [Equiv.apply_symm_apply] at h
  rw [← h]
  constructor
  · rintro ⟨c, hc, hm⟩
    exact ⟨c, hc, fun m => hm m (e.symm (mark m)) (e.apply_symm_apply _)⟩
  · rintro ⟨c, hc, hm⟩
    refine ⟨c, hc, ?_⟩
    intro m d hd
    have hmd := hm m
    change c (source.edgeOf (e.symm (mark m))) = value m at hmd
    rw [← hd, Equiv.symm_apply_apply] at hmd
    exact hmd

end Mettapedia.GraphTheory.FourColor.FrozenDartTransport
