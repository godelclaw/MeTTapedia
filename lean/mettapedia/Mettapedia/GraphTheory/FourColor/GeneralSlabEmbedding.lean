import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding

/-!
# The slab lemma for a slab of arbitrary shape

`TubeSlabEmbedding` proves the slab lemma for the zigzag ring.  Here the same
statement is proved for a copy of an arbitrary two-sided tangle `T` with `Fin k`
ports on both sides (`SlabOf T inner`): the side enlarged by the slab accepts a
word on the out-ports iff the side accepts some word on the in-port partners
with the pair in `T`'s relation (`SlabOf.mem_sideSupport_inner'_iff`).  Rungs
of thin annuli, armchair rings and periodic strips of any tiling are instances;
each needs only its own closed form and kernel table for stabilisation.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem.{u, u, u} V E) {k : Nat} [NeZero k]

/-! ## A slab of arbitrary shape attached to a side -/

/-- the darts of an abstract two-sided tangle with `Fin k` ports on both sides -/
abbrev SlabDart {Vt It : Type u} (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)) : Type u :=
  It ⊕ (Fin k ⊕ Fin k)

/-- a copy of the abstract tangle `T` sitting in the rotation system next to the side
`inner`: an injection of its darts with its incidences, in-ports attached to exactly the
boundary darts of `inner`, out-ports leaving the union -/
structure SlabOf {Vt It : Type u} (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k))
    (inner : V → Prop) where
  ι : SlabDart T → RS.D
  vtx : Vt → V
  ι_inj : Function.Injective ι
  vtx_inj : Function.Injective vtx
  vtx_not_inner : ∀ v, ¬ inner (vtx v)
  vert_ι : ∀ x, RS.vertOf (ι x) = vtx (T.vertOf x)
  alpha_interior : ∀ x : It, RS.alpha (ι (Sum.inl x)) = ι (Sum.inl (T.interiorAlpha x))
  in_inner : ∀ i, inner (RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inl i)))))
  out_not_inner : ∀ i, ¬ inner (RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inr i)))))
  out_not_slab : ∀ i v, RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inr i)))) ≠ vtx v
  cubic_slab : ∀ y : RS.D, (∃ v, RS.vertOf y = vtx v) → ∃ x, ι x = y
  boundary_inner : ∀ b : BoundaryDart RS inner, ∃ i, b.1.1 = RS.alpha (ι (Sum.inr (Sum.inl i)))

namespace SlabOf

variable {RS} {Vt It : Type u} {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)}
  {inner : V → Prop} (S : SlabOf RS T inner)

/-- the enlarged side -/
def inner' : V → Prop := fun v => inner v ∨ ∃ u, v = S.vtx u

theorem inner'_of_inner {v : V} (h : inner v) : S.inner' v := Or.inl h

theorem slab_inner' (x : SlabDart T) : S.inner' (RS.vertOf (S.ι x)) :=
  Or.inr ⟨_, S.vert_ι x⟩

theorem slab_not_inner (x : SlabDart T) : ¬ inner (RS.vertOf (S.ι x)) := by
  rw [S.vert_ι]; exact S.vtx_not_inner _

/-- the in-port's partner is a boundary dart of `inner` -/
def inPartner (i : Fin k) : BoundaryDart RS inner :=
  ⟨⟨RS.alpha (S.ι (Sum.inr (Sum.inl i))), S.in_inner i⟩, by
    rw [RS.alpha_involutive]; exact S.slab_not_inner _⟩

theorem inPartner_injective : Function.Injective S.inPartner := by
  intro i j h
  have h1 : RS.alpha (S.ι (Sum.inr (Sum.inl i))) = RS.alpha (S.ι (Sum.inr (Sum.inl j))) :=
    congrArg (fun b : BoundaryDart RS inner => b.1.1) h
  exact Sum.inl.inj (Sum.inr.inj (S.ι_inj (RS.alpha.injective h1)))

theorem inPartner_surjective : Function.Surjective S.inPartner := by
  intro b
  obtain ⟨i, hi⟩ := S.boundary_inner b
  exact ⟨i, Subtype.ext (Subtype.ext hi.symm)⟩

/-- the out-port is a boundary dart of the enlarged side -/
def outPort (i : Fin k) : BoundaryDart RS S.inner' :=
  ⟨⟨S.ι (Sum.inr (Sum.inr i)), S.slab_inner' _⟩, by
    rintro (h | ⟨v, hv⟩)
    · exact S.out_not_inner i h
    · exact S.out_not_slab i v hv⟩

theorem outPort_injective : Function.Injective S.outPort := by
  intro i j h
  have h1 : S.ι (Sum.inr (Sum.inr i)) = S.ι (Sum.inr (Sum.inr j)) :=
    congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) h
  exact Sum.inr.inj (Sum.inr.inj (S.ι_inj h1))

/-- every boundary dart of the enlarged side is an out-port -/
theorem outPort_surjective : Function.Surjective S.outPort := by
  intro b
  obtain ⟨⟨x, hx⟩, hb⟩ := b
  rcases hx with hx | ⟨v, hv⟩
  · exfalso
    let hbd : BoundaryDart RS inner := ⟨⟨x, hx⟩, fun h => hb (Or.inl h)⟩
    obtain ⟨i, hi⟩ := S.boundary_inner hbd
    apply hb
    have : RS.alpha x = S.ι (Sum.inr (Sum.inl i)) := by
      have := congrArg RS.alpha hi
      rwa [RS.alpha_involutive] at this
    rw [this]
    exact S.slab_inner' _
  · obtain ⟨y, hy⟩ := S.cubic_slab x ⟨v, hv⟩
    rcases y with y | i | i
    · exfalso
      apply hb
      subst hy
      show S.inner' (RS.vertOf (RS.alpha (S.ι (Sum.inl y))))
      rw [S.alpha_interior]
      exact S.slab_inner' _
    · exfalso
      apply hb
      subst hy
      exact Or.inl (S.in_inner i)
    · exact ⟨i, Subtype.ext (Subtype.ext hy)⟩

/-- boundary darts of `inner` are the in-port partners -/
noncomputable def inEquiv : Fin k ≃ BoundaryDart RS inner :=
  Equiv.ofBijective S.inPartner ⟨S.inPartner_injective, S.inPartner_surjective⟩

/-- boundary darts of the enlarged side are the out-ports -/
noncomputable def outEquiv : Fin k ≃ BoundaryDart RS S.inner' :=
  Equiv.ofBijective S.outPort ⟨S.outPort_injective, S.outPort_surjective⟩

/-! ## Restriction: a colouring of the enlarged side gives a ring colouring and a colouring of `inner` -/

/-- a ring dart, as a retained dart of the enlarged side -/
def slabDart (x : SlabDart T) : RetainedDart RS S.inner' := ⟨S.ι x, S.slab_inner' x⟩

/-- the in-port partner, as a retained dart of the enlarged side -/
def inPartnerDart' (i : Fin k) : RetainedDart RS S.inner' :=
  ⟨RS.alpha (S.ι (Sum.inr (Sum.inl i))), Or.inl (S.in_inner i)⟩

theorem outEquiv_symm_outPort (i : Fin k) : S.outEquiv.symm (S.outPort i) = i := by
  simp [outEquiv, Equiv.ofBijective_symm_apply_apply]

theorem inEquiv_symm_inPartner (i : Fin k) : S.inEquiv.symm (S.inPartner i) = i := by
  simp [inEquiv, Equiv.ofBijective_symm_apply_apply]

/-- restrict a colouring of the enlarged side to `inner` -/
def restrict (c : SideColoring RS S.inner') : SideColoring RS inner where
  color d := c.color ⟨d.1, Or.inl d.2⟩
  alpha_internal d h := c.alpha_internal ⟨d.1, Or.inl d.2⟩ (Or.inl h)
  ne_zero _ := c.ne_zero _
  proper _ _ hv hne :=
    c.proper _ _ hv (fun h => hne (Subtype.ext (Subtype.mk.inj h)))

/-- the ring colouring read off the slab -/
def ringColoring (c : SideColoring RS S.inner') : SlabDart T → Color :=
  fun x => c.color (S.slabDart x)

theorem color_inPartnerDart' (c : SideColoring RS S.inner') (i : Fin k) :
    c.color (S.inPartnerDart' i) = c.color (S.slabDart (Sum.inr (Sum.inl i))) :=
  c.alpha_internal (S.slabDart (Sum.inr (Sum.inl i))) (Or.inl (S.in_inner i))

theorem ringColoring_isTait (c : SideColoring RS S.inner') :
    T.IsTaitColoring (S.ringColoring c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show c.color (S.slabDart (Sum.inl (T.interiorAlpha x))) = c.color (S.slabDart (Sum.inl x))
    have hd : S.slabDart (Sum.inl (T.interiorAlpha x)) =
        ⟨RS.alpha (S.ι (Sum.inl x)), by rw [S.alpha_interior]; exact S.slab_inner' _⟩ :=
      Subtype.ext (S.alpha_interior x).symm
    rw [hd]
    exact c.alpha_internal (S.slabDart (Sum.inl x)) _
  · intro x x' hv hne
    apply c.proper
    · show RS.vertOf (S.ι x) = RS.vertOf (S.ι x')
      rw [S.vert_ι, S.vert_ι, hv]
    · intro h
      exact hne (S.ι_inj (congrArg Subtype.val h))
  · intro x
    exact c.ne_zero _

/-- **restriction**: the enlarged side's words are ring images of `inner`'s words -/
theorem exists_of_mem_sideSupport_inner' (w' : Fin k → Color)
    (h : (fun b => w' (S.outEquiv.symm b)) ∈ sideSupport RS S.inner') :
    ∃ w : Fin k → Color, (fun b => w (S.inEquiv.symm b)) ∈ sideSupport RS inner ∧
      T.AcceptsBoundaryWords w w' := by
  obtain ⟨c, hc⟩ := h
  let w : Fin k → Color := fun i => c.color (S.slabDart (Sum.inr (Sum.inl i)))
  refine ⟨w, ⟨S.restrict c, ?_⟩, S.ringColoring c, S.ringColoring_isTait c, ?_, ?_⟩
  · intro b
    obtain ⟨i, rfl⟩ := S.inPartner_surjective b
    show c.color (S.inPartnerDart' i) = w (S.inEquiv.symm (S.inPartner i))
    rw [inEquiv_symm_inPartner, color_inPartnerDart']
  · funext i; rfl
  · funext i
    show c.color (S.slabDart (Sum.inr (Sum.inr i))) = w' i
    have := hc (S.outPort i)
    simp only [outEquiv_symm_outPort] at this
    exact this

/-! ## Gluing: a colouring of `inner` and a ring colouring with matching seam give a colouring of the enlarged side -/

theorem exists_slab_of_not_inner (x : RetainedDart RS S.inner') (h : ¬ inner (RS.vertOf x.1)) :
    ∃ y, S.ι y = x.1 := by
  rcases x.2 with hx | ⟨v, hv⟩
  · exact absurd hx h
  · exact S.cubic_slab x.1 ⟨v, hv⟩

variable (c₀ : SideColoring RS inner) (rc : SlabDart T → Color)

open Classical in
/-- the glued colouring: `c₀` on `inner`, `rc` on the slab -/
noncomputable def glueColor (x : RetainedDart RS S.inner') : Color :=
  if h : inner (RS.vertOf x.1) then c₀.color ⟨x.1, h⟩
  else rc (Classical.choose (S.exists_slab_of_not_inner x h))

theorem glueColor_inner (x : RetainedDart RS S.inner') (h : inner (RS.vertOf x.1)) :
    S.glueColor c₀ rc x = c₀.color ⟨x.1, h⟩ := by
  unfold glueColor; rw [dif_pos h]

theorem glueColor_slab (y : SlabDart T) : S.glueColor c₀ rc (S.slabDart y) = rc y := by
  unfold glueColor
  rw [dif_neg (show ¬ inner (RS.vertOf (S.slabDart y).1) from S.slab_not_inner y)]
  congr 1
  apply S.ι_inj
  exact Classical.choose_spec (S.exists_slab_of_not_inner (S.slabDart y) (S.slab_not_inner y))

theorem inPartnerDart'_eq_alpha_slabDart (i : Fin k) :
    S.inPartnerDart' i = ⟨RS.alpha (S.slabDart (Sum.inr (Sum.inl i))).1, Or.inl (S.in_inner i)⟩ :=
  rfl

/-- **gluing** -/
theorem mem_sideSupport_inner'_of (w w' : Fin k → Color)
    (hw : ∀ i, c₀.color (S.inPartner i).1 = w i)
    (hrc : T.IsTaitColoring rc)
    (hl : ∀ i, rc (Sum.inr (Sum.inl i)) = w i)
    (hr : ∀ i, rc (Sum.inr (Sum.inr i)) = w' i) :
    (fun b => w' (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' := by
  obtain ⟨halpha, hvert, hnz⟩ := hrc
  refine ⟨⟨S.glueColor c₀ rc, ?_, ?_, ?_⟩, ?_⟩
  · intro x h
    by_cases hx : inner (RS.vertOf x.1)
    · by_cases hp : inner (RS.vertOf (RS.alpha x.1))
      · rw [S.glueColor_inner c₀ rc _ hp, S.glueColor_inner c₀ rc _ hx]
        exact c₀.alpha_internal ⟨x.1, hx⟩ hp
      · obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner ⟨RS.alpha x.1, h⟩ hp
        rcases y with y | i | i
        · exfalso
          have := S.slab_not_inner (Sum.inl (T.interiorAlpha y))
          rw [← S.alpha_interior, hy, RS.alpha_involutive] at this
          exact this hx
        · have hx1 : x.1 = RS.alpha (S.ι (Sum.inr (Sum.inl i))) := by
            rw [hy, RS.alpha_involutive]
          have h1 : (⟨RS.alpha x.1, h⟩ : RetainedDart RS S.inner') =
              S.slabDart (Sum.inr (Sum.inl i)) := Subtype.ext hy.symm
          rw [h1, S.glueColor_slab, hl, S.glueColor_inner c₀ rc _ hx, ← hw i]
          congr 1
          exact Subtype.ext hx1.symm
        · exfalso
          apply S.out_not_inner i
          rw [hy, RS.alpha_involutive]
          exact hx
    · obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner x hx
      have hxd : x = S.slabDart y := Subtype.ext hy.symm
      subst hxd
      rcases y with y | i | i
      · have h1 : (⟨RS.alpha (S.slabDart (Sum.inl y)).1, h⟩ : RetainedDart RS S.inner') =
            S.slabDart (Sum.inl (T.interiorAlpha y)) := by
          apply Subtype.ext
          show RS.alpha (S.ι (Sum.inl y)) = S.ι (Sum.inl (T.interiorAlpha y))
          exact S.alpha_interior y
        rw [h1, S.glueColor_slab, S.glueColor_slab]
        exact halpha y
      · have hp : inner (RS.vertOf (RS.alpha (S.slabDart (Sum.inr (Sum.inl i))).1)) :=
          S.in_inner i
        rw [S.glueColor_inner c₀ rc _ hp, S.glueColor_slab, hl, ← hw i]
        rfl
      · exfalso
        exact (S.outPort i).2 h
  · intro x
    by_cases hx : inner (RS.vertOf x.1)
    · rw [S.glueColor_inner c₀ rc _ hx]; exact c₀.ne_zero _
    · obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner x hx
      rw [show x = S.slabDart y from Subtype.ext hy.symm, S.glueColor_slab]
      exact hnz y
  · intro x x' hv hne
    by_cases hx : inner (RS.vertOf x.1) <;> by_cases hx' : inner (RS.vertOf x'.1)
    · rw [S.glueColor_inner c₀ rc _ hx, S.glueColor_inner c₀ rc _ hx']
      exact c₀.proper _ _ hv (fun h => hne (Subtype.ext (Subtype.mk.inj h)))
    · exfalso
      obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner x' hx'
      apply S.slab_not_inner y
      rw [hy, ← hv]; exact hx
    · exfalso
      obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner x hx
      apply S.slab_not_inner y
      rw [hy, hv]; exact hx'
    · obtain ⟨y, hy⟩ := S.exists_slab_of_not_inner x hx
      obtain ⟨y', hy'⟩ := S.exists_slab_of_not_inner x' hx'
      rw [show x = S.slabDart y from Subtype.ext hy.symm,
        show x' = S.slabDart y' from Subtype.ext hy'.symm, S.glueColor_slab, S.glueColor_slab]
      apply hvert
      · apply S.vtx_inj
        rw [← S.vert_ι, ← S.vert_ι, hy, hy']
        exact hv
      · intro h
        apply hne
        rw [show x = S.slabDart y from Subtype.ext hy.symm,
          show x' = S.slabDart y' from Subtype.ext hy'.symm, h]
  · intro b
    obtain ⟨i, rfl⟩ := S.outPort_surjective b
    show S.glueColor c₀ rc (S.slabDart (Sum.inr (Sum.inr i))) = w' (S.outEquiv.symm (S.outPort i))
    rw [S.glueColor_slab, hr, outEquiv_symm_outPort]

/-- **The slab lemma.**  The enlarged side accepts `w'` iff `inner` accepts some `w`
with `(w, w')` in the ring relation. -/
theorem mem_sideSupport_inner'_iff (w' : Fin k → Color) :
    (fun b => w' (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' ↔
      ∃ w : Fin k → Color, (fun b => w (S.inEquiv.symm b)) ∈ sideSupport RS inner ∧
        T.AcceptsBoundaryWords w w' := by
  constructor
  · exact S.exists_of_mem_sideSupport_inner' w'
  · rintro ⟨w, ⟨c₀, hc₀⟩, rc, hrc, hl, hr⟩
    refine S.mem_sideSupport_inner'_of c₀ rc w w' ?_ hrc (fun i => congrFun hl i)
      (fun i => congrFun hr i)
    intro i
    have := hc₀ (S.inPartner i)
    simp only [inEquiv_symm_inPartner] at this
    exact this

end SlabOf

end TubeSlab
end Mettapedia.GraphTheory.FourColor
