import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge
import Mettapedia.GraphTheory.FourColor.ZigzagRingComposite

/-!
# Vertex sides as dart colourings

The compositional stack reads the Tait support of a vertex side `keep` of a
rotation system through `OpenTangleData.ofVertexSide`, `rightClosedPortTangle`
and `innerSupport`.  Unfolded, a colouring of that tangle is a colour on every
dart at a kept vertex, invariant on internal edges, nonzero, and proper at
vertices (`SideColoring`); the support is the set of words it reads on the
boundary darts (`sideSupport`).  `mem_innerSupport_ofVertexSide_iff` is that
identification, which lets the tube-slab embedding be stated on dart
functions of the ambient rotation system.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ClosedCountReplacement
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem.{u, u, u} V E) (keep : V → Prop)

/-- a colour on every dart at a kept vertex: invariant on internal edges,
nonzero, proper at vertices -/
structure SideColoring where
  color : RetainedDart RS keep → Color
  alpha_internal : ∀ (d : RetainedDart RS keep) (h : keep (RS.vertOf (RS.alpha d.1))),
    color ⟨RS.alpha d.1, h⟩ = color d
  ne_zero : ∀ d, color d ≠ 0
  proper : ∀ d d' : RetainedDart RS keep, RS.vertOf d.1 = RS.vertOf d'.1 → d ≠ d' →
    color d ≠ color d'

/-- the words a side reads on its boundary darts -/
def sideSupport : Set (BoundaryDart RS keep → Color) :=
  {w | ∃ c : SideColoring RS keep, ∀ b : BoundaryDart RS keep, c.color b.1 = w b}

theorem equiv_internal (i : InternalDart RS keep) :
    retainedDartEquivInternalSumBoundary RS keep i.1 = Sum.inl i :=
  (retainedDartEquivInternalSumBoundary RS keep).apply_symm_apply (Sum.inl i)

theorem equiv_boundary (b : BoundaryDart RS keep) :
    retainedDartEquivInternalSumBoundary RS keep b.1 = Sum.inr b :=
  (retainedDartEquivInternalSumBoundary RS keep).apply_symm_apply (Sum.inr b)

theorem internal_ne_boundary (i : InternalDart RS keep) (b : BoundaryDart RS keep) :
    i.1 ≠ b.1 := by
  intro h
  exact b.2 (h ▸ i.2)

theorem eq_of_equiv_inl {d : RetainedDart RS keep} {i : InternalDart RS keep}
    (hd : retainedDartEquivInternalSumBoundary RS keep d = Sum.inl i) : d = i.1 := by
  have := congrArg (retainedDartEquivInternalSumBoundary RS keep).symm hd
  rw [Equiv.symm_apply_apply] at this
  exact this

theorem eq_of_equiv_inr {d : RetainedDart RS keep} {b : BoundaryDart RS keep}
    (hd : retainedDartEquivInternalSumBoundary RS keep d = Sum.inr b) : d = b.1 := by
  have := congrArg (retainedDartEquivInternalSumBoundary RS keep).symm hd
  rw [Equiv.symm_apply_apply] at this
  exact this

/-- **The stack's inner support is the side support.** -/
theorem mem_innerSupport_ofVertexSide_iff {L : Type u} (outer : RetainedDart RS keep)
    (m : L ≃ BoundaryDart RS keep) (y : L → Color) :
    y ∈ innerSupport (rightClosedPortTangle (OpenTangleData.ofVertexSide RS keep outer) m) ↔
      (fun b => y (m.symm b)) ∈ sideSupport RS keep := by
  constructor
  · rintro ⟨⟨c, ⟨hnz, hproper⟩, hword⟩⟩
    let e := retainedDartEquivInternalSumBoundary RS keep
    let color : RetainedDart RS keep → Color := fun d =>
      Sum.elim (fun i => c.color (Sum.inl i))
        (fun b => c.color (Sum.inr (Sum.inl (m.symm b)))) (e d)
    have hint : ∀ i : InternalDart RS keep, color i.1 = c.color (Sum.inl i) := fun i => by
      simp only [color, e, equiv_internal, Sum.elim_inl]
    have hbd : ∀ b : BoundaryDart RS keep,
        color b.1 = c.color (Sum.inr (Sum.inl (m.symm b))) := fun b => by
      simp only [color, e, equiv_boundary, Sum.elim_inr]
    refine ⟨⟨color, ?_, ?_, ?_⟩, ?_⟩
    · intro d h
      let i : InternalDart RS keep := ⟨d, h⟩
      let i' : InternalDart RS keep :=
        ⟨⟨RS.alpha d.1, h⟩, by simpa [RS.alpha_involutive] using d.2⟩
      have h1 : color ⟨RS.alpha d.1, h⟩ = c.color (Sum.inl i') := hint i'
      have h2 : color d = c.color (Sum.inl i) := hint i
      rw [h1, h2]
      exact c.invariant i
    · intro d
      rcases hd : e d with i | b
      · rw [eq_of_equiv_inl RS keep hd, hint]; exact hnz _
      · rw [eq_of_equiv_inr RS keep hd, hbd]; exact hnz _
    · intro d d' hv hne
      rcases hd : e d with i | b <;> rcases hd' : e d' with i' | b'
      · rw [eq_of_equiv_inl RS keep hd, eq_of_equiv_inl RS keep hd'] at hv hne ⊢
        rw [hint, hint]
        apply hproper
        · exact Subtype.ext hv
        · intro h; exact hne (congrArg Subtype.val (Sum.inl.inj h))
      · rw [eq_of_equiv_inl RS keep hd, eq_of_equiv_inr RS keep hd'] at hv hne ⊢
        rw [hint, hbd]
        apply hproper
        · show OpenTangleData.vertexSideVertex RS keep i.1 = OpenTangleData.vertexSideVertex RS keep (m (m.symm b')).1
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext hv
        · simp
      · rw [eq_of_equiv_inr RS keep hd, eq_of_equiv_inl RS keep hd'] at hv hne ⊢
        rw [hbd, hint]
        apply hproper
        · show OpenTangleData.vertexSideVertex RS keep (m (m.symm b)).1 = OpenTangleData.vertexSideVertex RS keep i'.1
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext hv
        · simp
      · rw [eq_of_equiv_inr RS keep hd, eq_of_equiv_inr RS keep hd'] at hv hne ⊢
        rw [hbd, hbd]
        apply hproper
        · show OpenTangleData.vertexSideVertex RS keep (m (m.symm b)).1 = OpenTangleData.vertexSideVertex RS keep (m (m.symm b')).1
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact Subtype.ext hv
        · intro h
          apply hne
          have := m.symm.injective (Sum.inl.inj (Sum.inr.inj h))
          exact congrArg Subtype.val this
    · intro b
      show color b.1 = y (m.symm b)
      rw [hbd]
      exact congrFun hword (Sum.inl (m.symm b))
  · rintro ⟨c, hc⟩
    refine ⟨⟨⟨Sum.elim (fun i => c.color i.1)
      (Sum.elim (fun p => c.color (m p).1) PEmpty.elim), ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩
    · intro i
      simp only [Sum.elim_inl]
      exact c.alpha_internal i.1 _
    · rintro (i | p | e)
      · exact c.ne_zero _
      · exact c.ne_zero _
      · exact e.elim
    · rintro (i | p | e) (i' | p' | e') hv hne
      · exact c.proper _ _ (congrArg Subtype.val hv)
          (fun h => hne (congrArg Sum.inl (Subtype.ext h)))
      · exact c.proper _ _ (congrArg Subtype.val hv) (internal_ne_boundary RS keep i (m p'))
      · exact e'.elim
      · exact c.proper _ _ (congrArg Subtype.val hv)
          (internal_ne_boundary RS keep i' (m p)).symm
      · exact c.proper _ _ (congrArg Subtype.val hv)
          (fun h => hne (by
            have := m.injective (Subtype.ext h)
            rw [this]))
      · exact e'.elim
      · exact e.elim
      · exact e.elim
      · exact e.elim
    · funext p
      rcases p with q | e
      · simp only [word, Sum.elim_inl, Sum.elim_inr]
        rw [hc (m q)]
        simp
      · exact e.elim

/-! ## A zigzag slab attached to a side -/

open ZigzagRing in
/-- a `(k,0)` zigzag ring sitting in the rotation system next to the side `inner`:
an injection of the abstract ring's darts, with the ring's incidences, in-ports
attached to exactly the boundary darts of `inner`, out-ports leaving the union -/
structure ZigzagSlab (k : Nat) [NeZero k] (inner : V → Prop) where
  ι : AllDart k → RS.D
  vtx : Vtx k → V
  ι_inj : Function.Injective ι
  vtx_inj : Function.Injective vtx
  vtx_not_inner : ∀ v, ¬ inner (vtx v)
  vert_ι : ∀ x, RS.vertOf (ι x) = vtx ((ring k).vertOf x)
  alpha_interior : ∀ x : Dart k, RS.alpha (ι (Sum.inl x)) = ι (Sum.inl (flip k x))
  in_inner : ∀ i, inner (RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inl i)))))
  out_not_inner : ∀ i, ¬ inner (RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inr i)))))
  out_not_slab : ∀ i v, RS.vertOf (RS.alpha (ι (Sum.inr (Sum.inr i)))) ≠ vtx v
  cubic_slab : ∀ y : RS.D, (∃ v, RS.vertOf y = vtx v) → ∃ x, ι x = y
  boundary_inner : ∀ b : BoundaryDart RS inner, ∃ i, b.1.1 = RS.alpha (ι (Sum.inr (Sum.inl i)))

namespace ZigzagSlab

open ZigzagRing

variable {RS} {k : Nat} [NeZero k] {inner : V → Prop} (S : ZigzagSlab RS k inner)

/-- the enlarged side -/
def inner' : V → Prop := fun v => inner v ∨ ∃ u, v = S.vtx u

theorem inner'_of_inner {v : V} (h : inner v) : S.inner' v := Or.inl h

theorem slab_inner' (x : AllDart k) : S.inner' (RS.vertOf (S.ι x)) :=
  Or.inr ⟨_, S.vert_ι x⟩

theorem slab_not_inner (x : AllDart k) : ¬ inner (RS.vertOf (S.ι x)) := by
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
def slabDart (x : AllDart k) : RetainedDart RS S.inner' := ⟨S.ι x, S.slab_inner' x⟩

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
def ringColoring (c : SideColoring RS S.inner') : AllDart k → Color :=
  fun x => c.color (S.slabDart x)

theorem color_inPartnerDart' (c : SideColoring RS S.inner') (i : Fin k) :
    c.color (S.inPartnerDart' i) = c.color (S.slabDart (Sum.inr (Sum.inl i))) :=
  c.alpha_internal (S.slabDart (Sum.inr (Sum.inl i))) (Or.inl (S.in_inner i))

theorem ringColoring_isTait (c : SideColoring RS S.inner') :
    (ring k).IsTaitColoring (S.ringColoring c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show c.color (S.slabDart (Sum.inl (flip k x))) = c.color (S.slabDart (Sum.inl x))
    have hd : S.slabDart (Sum.inl (flip k x)) =
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
      (ring k).AcceptsBoundaryWords w w' := by
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

end ZigzagSlab

end TubeSlab
end Mettapedia.GraphTheory.FourColor
