import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding

/-!
# Parity and colour symmetry of a side's boundary words

Every word a cubic side accepts has zero colour sum (each vertex contributes the
three distinct nonzero colours, whose sum is zero; interior edges are counted
twice), and the accepted words are invariant under every zero-fixing bijection
of the colours.  These two facts compress the finite state of a node: its
support is a union of colour orbits inside the zero-sum words.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {keep : V → Prop}

theorem color_add_self (x : Color) : x + x = 0 := by
  rcases x with ⟨a, b⟩; ext <;> simp

theorem sum_nonzero_colors : ∑ c ∈ (Finset.univ : Finset Color).erase 0, c = 0 := by decide

theorem card_color' : Fintype.card Color = 4 := rfl

theorem mem_dartsAt {v : V} {d : RS.D} (hd : d ∈ RS.dartsAt v) : RS.vertOf d = v :=
  (Finset.mem_filter.mp hd).2

/-! ## Colour symmetry -/

namespace SideColoring

/-- a zero-fixing colour bijection applied to a side colouring -/
def relabel (c : SideColoring RS keep) (σ : Color ≃ Color) (hσ : σ 0 = 0) :
    SideColoring RS keep where
  color d := σ (c.color d)
  alpha_internal d h := congrArg σ (c.alpha_internal d h)
  ne_zero d h := c.ne_zero d (σ.injective (h.trans hσ.symm))
  proper d d' hv hne h := c.proper d d' hv hne (σ.injective h)

end SideColoring

theorem relabel_mem_sideSupport {w : BoundaryDart RS keep → Color} (σ : Color ≃ Color)
    (hσ : σ 0 = 0) (h : w ∈ sideSupport RS keep) :
    (fun b => σ (w b)) ∈ sideSupport RS keep := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.relabel σ hσ, fun b => by show σ (c.color b.1) = σ (w b); rw [hc b]⟩

theorem symm_zero {σ : Color ≃ Color} (hσ : σ 0 = 0) : σ.symm 0 = 0 :=
  (Equiv.symm_apply_eq σ).mpr hσ.symm

/-- **the accepted words are invariant under zero-fixing colour bijections** -/
theorem relabel_mem_sideSupport_iff (σ : Color ≃ Color) (hσ : σ 0 = 0)
    (w : BoundaryDart RS keep → Color) :
    (fun b => σ (w b)) ∈ sideSupport RS keep ↔ w ∈ sideSupport RS keep := by
  refine ⟨fun h => ?_, relabel_mem_sideSupport σ hσ⟩
  have := relabel_mem_sideSupport σ.symm (symm_zero hσ) h
  simpa using this

/-! ## Parity -/

open Classical in
/-- the colour of a dart, zero off the side -/
noncomputable def SideColoring.total (c : SideColoring RS keep) (d : RS.D) : Color :=
  if h : keep (RS.vertOf d) then c.color ⟨d, h⟩ else 0

open Classical in
theorem SideColoring.total_retained (c : SideColoring RS keep) (d : RetainedDart RS keep) :
    c.total d.1 = c.color d := by
  obtain ⟨d, hd⟩ := d
  unfold SideColoring.total; rw [dif_pos hd]

open Classical in
theorem SideColoring.total_of_not (c : SideColoring RS keep) {d : RS.D}
    (h : ¬ keep (RS.vertOf d)) : c.total d = 0 := by
  unfold SideColoring.total; rw [dif_neg h]

open Classical in
/-- at a cubic vertex of the side the three colours are distinct and nonzero, so they sum
to zero; off the side everything is zero -/
theorem SideColoring.sum_dartsAt (c : SideColoring RS keep) (hcubic : RS.IsCubic) (v : V) :
    ∑ d ∈ RS.dartsAt v, c.total d = 0 := by
  by_cases hv : keep v
  · have hmem : ∀ d ∈ RS.dartsAt v, keep (RS.vertOf d) := by
      intro d hd
      rw [mem_dartsAt hd]; exact hv
    have hinj : ∀ d ∈ RS.dartsAt v, ∀ d' ∈ RS.dartsAt v, c.total d = c.total d' → d = d' := by
      intro d hd d' hd' h
      by_contra hne
      have hd1 := hmem d hd
      have hd2 := hmem d' hd'
      rw [show c.total d = c.color ⟨d, hd1⟩ from c.total_retained ⟨d, hd1⟩,
        show c.total d' = c.color ⟨d', hd2⟩ from c.total_retained ⟨d', hd2⟩] at h
      refine c.proper ⟨d, hd1⟩ ⟨d', hd2⟩ ?_ (fun e => hne (congrArg Subtype.val e)) h
      show RS.vertOf d = RS.vertOf d'
      rw [mem_dartsAt hd, mem_dartsAt hd']
    have himage : (RS.dartsAt v).image c.total = (Finset.univ : Finset Color).erase 0 := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨d, hd, rfl⟩ := hx
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        rw [c.total_retained ⟨d, hmem d hd⟩]
        exact c.ne_zero _
      · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h), hcubic v,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_color']
    have := Finset.sum_image (f := fun x : Color => x) hinj
    rw [himage, sum_nonzero_colors] at this
    exact this.symm
  · apply Finset.sum_eq_zero
    intro d hd
    exact c.total_of_not (by rw [mem_dartsAt hd]; exact hv)

open Classical in
theorem SideColoring.sum_total (c : SideColoring RS keep) (hcubic : RS.IsCubic) :
    ∑ d, c.total d = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ RS.vertOf c.total]
  apply Finset.sum_eq_zero
  intro v _
  exact c.sum_dartsAt hcubic v

open Classical in
theorem SideColoring.sum_retained (c : SideColoring RS keep) (hcubic : RS.IsCubic) :
    ∑ d : RetainedDart RS keep, c.color d = 0 := by
  have h := c.sum_total hcubic
  rw [← Finset.sum_filter_of_ne (p := fun d => keep (RS.vertOf d)) (fun d _ hne => by
      by_contra hk; exact hne (c.total_of_not hk))] at h
  rw [Finset.sum_subtype (F := retainedDartFintype RS keep) _ (fun d => by simp) c.total] at h
  rw [← h]
  exact Finset.sum_congr rfl fun d _ => (c.total_retained d).symm

open Classical in
/-- interior darts pair up with equal colours -/
theorem SideColoring.sum_internal (c : SideColoring RS keep) :
    ∑ i : InternalDart RS keep, c.color i.1 = 0 := by
  apply Finset.sum_involution (fun i _ => internalAlpha RS keep i)
  · intro i _
    have : c.color (internalAlpha RS keep i).1 = c.color i.1 := c.alpha_internal i.1 i.2
    rw [this, color_add_self]
  · intro i _ _ h
    apply RS.alpha_fixfree i.1.1
    have := congrArg (fun j : InternalDart RS keep => j.1.1) h
    exact this
  · intro i _; exact Finset.mem_univ _
  · intro i _
    apply Subtype.ext; apply Subtype.ext
    exact RS.alpha_involutive i.1.1

open Classical in
/-- **the boundary word of a cubic side sums to zero** -/
theorem SideColoring.sum_boundary (c : SideColoring RS keep) (hcubic : RS.IsCubic) :
    ∑ b : BoundaryDart RS keep, c.color b.1 = 0 := by
  have h := c.sum_retained hcubic
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun d : RetainedDart RS keep => keep (RS.vertOf (RS.alpha d.1)))] at h
  rw [Finset.sum_subtype (F := internalDartFintype RS keep) _ (fun d => by simp)
      (fun d => c.color d),
    Finset.sum_subtype (F := boundaryDartFintype RS keep) _ (fun d => by simp)
      (fun d => c.color d)] at h
  have key : (∑ a : InternalDart RS keep, c.color a.1) +
      (∑ b : BoundaryDart RS keep, c.color b.1) = 0 := h
  rw [c.sum_internal, zero_add] at key
  exact key

theorem sum_eq_zero_of_mem_sideSupport (hcubic : RS.IsCubic) {w : BoundaryDart RS keep → Color}
    (h : w ∈ sideSupport RS keep) : ∑ b, w b = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [← c.sum_boundary hcubic]
  exact Finset.sum_congr rfl fun b _ => (hc b).symm

end TubeSlab
end Mettapedia.GraphTheory.FourColor
