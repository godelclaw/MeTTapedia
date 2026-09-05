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

end TubeSlab
end Mettapedia.GraphTheory.FourColor
