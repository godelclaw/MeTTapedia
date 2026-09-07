import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge

/-!
# Joint cut-word and frozen-dart support

The support of a boundary word alone forgets its correlation with colours
prescribed on named darts. Here each side records the word together with
the entire prescription. An absent observation imposes no condition on
that side. Gluing requires the same prescription on both sides.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenCountSupport

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge

universe u v

/-- Literal dart observations, including labels not present in this piece. -/
def Observes {D : Type*} {M : Type v} (color : D → Color)
    (obs : M → Option D) (value : M → Color) : Prop :=
  ∀ m d, obs m = some d → color d = value m

theorem observes_map_iff {D D' : Type*} (f : D → D') (color : D' → Color)
    {M : Type v} (obs : M → Option D) (value : M → Color) :
    Observes color (fun m => (obs m).map f) value ↔
      Observes (fun d => color (f d)) obs value := by
  constructor
  · intro h m d hd
    exact h m (f d) (by simp [hd])
  · intro h m d hd
    cases ho : obs m with
    | none => simp [ho] at hd
    | some e =>
      have he : f e = d := by simpa [ho] using hd
      exact he ▸ h m e ho

variable {V W W' I J J' L : Type u} {M : Type v}

def innerJointSupport (T : PortTangle W J (L ⊕ EmptyPort.{u}))
    (obs : M → Option (J ⊕ (L ⊕ EmptyPort.{u}))) :
    Set ((L → Color) × (M → Color)) :=
  {p | ∃ c : Col T (Sum.elim p.1 PEmpty.elim), Observes c.val.color obs p.2}

def outerJointSupport (T : PortTangle V I (EmptyPort.{u} ⊕ L))
    (obs : M → Option (I ⊕ (EmptyPort.{u} ⊕ L))) :
    Set ((L → Color) × (M → Color)) :=
  {p | ∃ c : Col T (Sum.elim PEmpty.elim p.1), Observes c.val.color obs p.2}

/-- Acceptance of a fixed prescription on the actual closed Count composite. -/
def ClosedAccepts (left : PortTangle V I (EmptyPort.{u} ⊕ L))
    (right : PortTangle W J (L ⊕ EmptyPort.{u}))
    (lo : M → Option (I ⊕ (EmptyPort.{u} ⊕ L)))
    (ro : M → Option (J ⊕ (L ⊕ EmptyPort.{u}))) (value : M → Color) : Prop :=
  ∃ c : Col (series left right) (Sum.elim PEmpty.elim PEmpty.elim),
    Observes (restrict₁ left right c.val).color lo value ∧
    Observes (restrict₂ left right c.val).color ro value

/-- The gluing bijection keeps the full frozen prescription, not just the
projection of the joint support to cut words. -/
theorem closedAccepts_iff (left : PortTangle V I (EmptyPort.{u} ⊕ L))
    (right : PortTangle W J (L ⊕ EmptyPort.{u}))
    (lo : M → Option (I ⊕ (EmptyPort.{u} ⊕ L)))
    (ro : M → Option (J ⊕ (L ⊕ EmptyPort.{u}))) (value : M → Color) :
    ClosedAccepts left right lo ro value ↔ ∃ word : L → Color,
      (word, value) ∈ outerJointSupport left lo ∧
      (word, value) ∈ innerJointSupport right ro := by
  constructor
  · rintro ⟨c, hl, hr⟩
    let p := gluingEquiv left right PEmpty.elim PEmpty.elim c
    exact ⟨p.1, ⟨p.2.1, hl⟩, ⟨p.2.2, hr⟩⟩
  · rintro ⟨word, ⟨cl, hl⟩, ⟨cr, hr⟩⟩
    let c := (gluingEquiv left right PEmpty.elim PEmpty.elim).symm ⟨word, cl, cr⟩
    refine ⟨c, ?_, ?_⟩
    · change Observes (restrict₁ left right (glueColoring left right cl.val cr.val)).color lo value
      rw [restrict₁_glueColoring]
      exact hl
    · change Observes (restrict₂ left right (glueColoring left right cl.val cr.val)).color ro value
      rw [restrict₂_glueColoring]
      · exact hr
      · intro p
        exact (congrFun cl.property.2 (Sum.inr p)).trans
          (congrFun cr.property.2 (Sum.inl p)).symm

/-- Equal joint supports preserve each fixed prescription separately. -/
theorem closedAccepts_iff_of_joint_eq (left : PortTangle V I (EmptyPort.{u} ⊕ L))
    (old : PortTangle W J (L ⊕ EmptyPort.{u}))
    (new : PortTangle W' J' (L ⊕ EmptyPort.{u}))
    (lo : M → Option (I ⊕ (EmptyPort.{u} ⊕ L)))
    (oo : M → Option (J ⊕ (L ⊕ EmptyPort.{u})))
    (no : M → Option (J' ⊕ (L ⊕ EmptyPort.{u})))
    (heq : innerJointSupport old oo = innerJointSupport new no) (value : M → Color) :
    ClosedAccepts left old lo oo value ↔ ClosedAccepts left new lo no value := by
  rw [closedAccepts_iff, closedAccepts_iff, heq]

end Mettapedia.GraphTheory.FourColor.FrozenCountSupport
