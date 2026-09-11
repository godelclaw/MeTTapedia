import Mettapedia.GraphTheory.FourColor.BoundarySmallCutViability

/-!
# Exact component change when attaching one vertex

Sew arbitrary old ports to a single new vertex. The resulting component
quotient consists of the untouched old components and one new merged
component. Thus `C_new + touched = C_old + 1`, including an empty seam,
hidden components, repeated attachment vertices, loops and parallel edges.
The number touched is read from the zero-cut profile on the consumed ports;
no connected-prefix or visibility premise is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.StarAttachmentComponents

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph
open BoundarySmallCutViability BoundarySmallCutProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E P : Type*} (G : Multigraph V E) (ports : P → V)

def vertex : Multigraph Unit Empty := ⟨Empty.elim, Empty.elim⟩

def attach : Multigraph (V ⊕ Unit) (E ⊕ Empty ⊕ P) :=
  glue G vertex ports (fun _ => ())

abbrev Component := Quotient (componentSetoid G)

def touched (q : Component G) : Prop :=
  ∃ p, Quotient.mk (componentSetoid G) (ports p) = q

def mark (q : Component G) : Option {q : Component G // ¬ touched G ports q} :=
  if h : touched G ports q then none else some ⟨q, h⟩

theorem mark_none (q : Component G) : mark G ports q = none ↔ touched G ports q := by
  simp [mark]

theorem mark_eq (q r : Component G) :
    mark G ports q = mark G ports r ↔ q = r ∨ touched G ports q ∧ touched G ports r := by
  by_cases hq : touched G ports q <;> by_cases hr : touched G ports r <;>
    simp [mark, hq, hr] <;> aesop

def label : V ⊕ Unit → Option {q : Component G // ¬ touched G ports q} :=
  Sum.elim (fun v => mark G ports (Quotient.mk (componentSetoid G) v)) (fun _ => none)

theorem label_edge (e : E ⊕ Empty ⊕ P) :
    label G ports ((attach G ports).fst e) = label G ports ((attach G ports).snd e) := by
  rcases e with e | e | p
  · change mark G ports _ = mark G ports _
    apply congrArg (mark G ports)
    exact Quotient.sound (s := componentSetoid G)
      (Relation.ReflTransGen.single ⟨e, not_false, .inl ⟨rfl, rfl⟩⟩)
  · exact e.elim
  · exact (mark_none G ports _).mpr ⟨p, rfl⟩

theorem label_of_reach {u v : V ⊕ Unit} (h : (attach G ports).Reach u v) :
    label G ports u = label G ports v := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨e, _, he⟩ := hs
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans (label_edge G ports e)
    · exact ih.trans (label_edge G ports e).symm

theorem reach_vertex {v : V} (h : touched G ports (Quotient.mk (componentSetoid G) v)) :
    (attach G ports).Reach (.inl v) (.inr ()) := by
  obtain ⟨p, hp⟩ := h
  have hv : G.Reach v (ports p) := Quotient.exact (s := componentSetoid G) hp.symm
  exact (glue_reach_inl (H := G) (K := vertex) (pH := ports) (pK := fun _ => ())
    (avoidG := fun _ => False) (avoidH := fun _ => False)
    (fun _ h => h) hv).trans (.single (glue_step_seam p not_false))

theorem reach_of_label {u v : V ⊕ Unit} (h : label G ports u = label G ports v) :
    (attach G ports).Reach u v := by
  rcases u with u | ⟨⟩ <;> rcases v with v | ⟨⟩
  · rcases (mark_eq G ports _ _).mp h with he | ⟨hu, hv⟩
    · exact glue_reach_inl (fun _ h => h) (Quotient.exact (s := componentSetoid G) he)
    · exact (reach_vertex G ports hu).trans (reach_symm (reach_vertex G ports hv))
  · exact reach_vertex G ports ((mark_none G ports _).mp h)
  · exact reach_symm (reach_vertex G ports ((mark_none G ports _).mp h.symm))
  · exact .refl

theorem reach_iff_label (u v : V ⊕ Unit) :
    (attach G ports).Reach u v ↔ label G ports u = label G ports v :=
  ⟨label_of_reach G ports, reach_of_label G ports⟩

theorem label_surjective : Function.Surjective (label G ports) := by
  rintro (_ | ⟨q, hq⟩)
  · exact ⟨.inr (), rfl⟩
  · obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    exact ⟨.inl v, by simp [label, mark, hq]⟩

/-- The new vertex is one component even when no old port is consumed. -/
def componentEquiv : Component (attach G ports) ≃
    Option {q : Component G // ¬ touched G ports q} := by
  let f : Component (attach G ports) → Option {q : Component G // ¬ touched G ports q} :=
    Quotient.lift (label G ports) (fun _ _ h => label_of_reach G ports h)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b he
    obtain ⟨u, rfl⟩ := Quotient.exists_rep a
    obtain ⟨v, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound (reach_of_label G ports he)
  · intro q
    obtain ⟨v, hv⟩ := label_surjective G ports q
    exact ⟨Quotient.mk (componentSetoid (attach G ports)) v, hv⟩

theorem component_count [Fintype V] :
    Nat.card (Component (attach G ports)) + Nat.card {q : Component G // touched G ports q} =
      Nat.card (Component G) + 1 := by
  letI : Fintype (Component G) := Fintype.ofFinite _
  have h := Nat.card_congr (componentEquiv G ports)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at h ⊢
  rw [h, Fintype.card_subtype_compl]
  have hle := Fintype.card_subtype_le (touched G ports)
  omega

variable [Fintype E]

/-- Only consumed ports are quotiented. Untouched and hidden components
need not be reconstructed from this restricted profile. -/
def touchedEquiv : Quotient (portSetoid (profile G ports)) ≃
    {q : Component G // touched G ports q} := by
  let f : Quotient (portSetoid (profile G ports)) → {q : Component G // touched G ports q} :=
    Quotient.lift (fun p => ⟨Quotient.mk (componentSetoid G) (ports p), p, rfl⟩)
      (fun p q h => Subtype.ext (Quotient.sound ((sameComponent_profile G ports p q).mp h)))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b he
    obtain ⟨p, rfl⟩ := Quotient.exists_rep a
    obtain ⟨q, rfl⟩ := Quotient.exists_rep b
    apply Quotient.sound
    apply (sameComponent_profile G ports p q).mpr
    exact Quotient.exact (s := componentSetoid G) (congrArg Subtype.val he)
  · rintro ⟨q, p, hp⟩
    exact ⟨Quotient.mk (portSetoid (profile G ports)) p, Subtype.ext hp⟩

theorem component_count_profile [Fintype V] :
    Nat.card (Component (attach G ports)) +
        Nat.card (Quotient (portSetoid (profile G ports))) = Nat.card (Component G) + 1 := by
  rw [Nat.card_congr (touchedEquiv G ports)]
  exact component_count G ports

end
end Mettapedia.GraphTheory.FourColor.StarAttachmentComponents
