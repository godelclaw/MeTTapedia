import Mettapedia.SetTheory.OpenTower.AntiFounded.Classification
import Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories

/-!
# What each candidate for the outermost set theory can host

A membership structure is a graph `r` on a type `α`: `r a b` says that `b` is a member of `a`.
*Hosting* it means an injective map into a set universe that keeps and reflects membership.

**The anti-founded universe hosts every graph.** Each node is sent to the decoration of the
graph extended by a *tag*: the node's image has, besides the images of its children, one extra
member `{Ω, s}`, with `s` a well-founded hyperset naming the node (`exists_membership_embedding`).
The tag is never the image of a node, so membership among the images is exactly `r`. The tags
come from a general decoration with parameters: every graph has a decoration in which each node
has one prescribed extra member (`mem_decorateWith`).

**Transitively, exactly the strongly extensional graphs.** A decoration is a copy that is
closed downward: the members of an image are the images of the children. A graph has an
injective decoration exactly when bisimilar nodes are equal (`exists_injective_decoration_iff`).
The two-node cycle is extensional (`twoCycle_extensional`) and not strongly extensional
(`not_stronglyExtensional_twoCycle`). So it has no injective decoration
(`not_exists_injective_decoration_twoCycle`): the anti-founded universe has no two distinct sets
each of which is the other's singleton (`eq_of_eq_singleton_of_eq_singleton`). Boffa's
anti-foundation axiom asks for exactly such sets. With tags, the two-node cycle is hosted
(`exists_tagged_twoCycle`): two distinct hypersets, each a member of the other and not of
itself.

**The well-founded sets host exactly well-founded graphs.** A membership-keeping map into
`ZFSet` makes the child relation well-founded (`wellFounded_of_zfset_embedding`), so no graph
with a cycle is hosted, the one-node loop among them (`not_exists_zfset_embedding_loop`).

**The two maximal admitted theories in one carrier.** The hypersets satisfy exactly the
anti-founded theory, and their well-founded part, with the same membership restricted,
satisfies the well-founded theory (`plural_family_in_one_carrier`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph
open Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
open Mettapedia.SetTheory.CarveOuts
open Mettapedia.SetTheory.Profiles

universe u

/-! ## Transitive copies: exactly the strongly extensional graphs -/

/-- **A graph has an injective decoration in the hypersets exactly when bisimilar nodes are
equal.** A decoration is a copy closed downward; anti-foundation identifies bisimilar nodes. -/
theorem exists_injective_decoration_iff {α : Type u} (r : α → α → Prop) :
    (∃ d : α → HSet.{u}, Function.Injective d ∧ HSet.IsDecoration r d) ↔
      ∀ a b, Bisimilar r r a b → a = b := by
  constructor
  · rintro ⟨d, injective, hd⟩ a b related
    apply injective
    rw [hd.eq_decorate]
    exact HSet.decorate_eq_of_bisimilar related
  · intro strong
    exact ⟨HSet.decorate r, fun a b equal => strong a b (HSet.decorate_eq_decorate_iff.mp equal),
      HSet.isDecoration_decorate r⟩

/-- The two-node cycle is extensional: distinct nodes have distinct children. -/
theorem twoCycle_extensional :
    ∀ a b : HSet.twoCycle.{u}.Node, (∀ c, HSet.twoCycle.edge a c ↔ HSet.twoCycle.edge b c) →
      a = b := by
  rintro ⟨a⟩ ⟨b⟩ same
  have h := (same ⟨!a⟩).mp rfl
  change (!a) = !b at h
  simp only [Bool.not_inj_iff] at h
  rw [h]

/-- The two-node cycle is not strongly extensional: its two nodes are bisimilar. -/
theorem not_stronglyExtensional_twoCycle :
    ¬ ∀ a b : HSet.twoCycle.{u}.Node, Bisimilar HSet.twoCycle.edge HSet.twoCycle.edge a b →
      a = b := by
  intro strong
  have related : Bisimilar HSet.twoCycle.edge HSet.twoCycle.edge
      (⟨true⟩ : HSet.twoCycle.{u}.Node) ⟨false⟩ :=
    ⟨fun _ _ => True, fun a b _ =>
      ⟨fun _ _ => ⟨⟨!b.down⟩, rfl, trivial⟩, fun _ _ => ⟨⟨!a.down⟩, rfl, trivial⟩⟩, trivial⟩
  have equal := strong _ _ related
  exact Bool.noConfusion (congrArg ULift.down equal)

/-- **The anti-founded universe has no injective decoration of the two-node cycle.** -/
theorem not_exists_injective_decoration_twoCycle :
    ¬ ∃ d : HSet.twoCycle.{u}.Node → HSet.{u}, Function.Injective d ∧
      HSet.IsDecoration HSet.twoCycle.edge d :=
  fun h => not_stronglyExtensional_twoCycle ((exists_injective_decoration_iff _).mp h)

/-- **Two sets, each the other's singleton, are equal** (both are `Ω`). -/
theorem eq_of_eq_singleton_of_eq_singleton {x y : HSet.{u}} (hx : x = {y}) (hy : y = {x}) :
    x = y := by
  let d : HSet.twoCycle.{u}.Node → HSet.{u} := fun a => if a.down then x else y
  have hd : HSet.IsDecoration HSet.twoCycle.edge d := by
    rintro ⟨a⟩ z
    cases a
    · change z ∈ y ↔ ∃ b : HSet.twoCycle.{u}.Node, b.down = true ∧ d b = z
      rw [hy, HSet.mem_singleton]
      exact ⟨fun h => ⟨⟨true⟩, rfl, h.symm⟩, fun ⟨⟨b⟩, hb, e⟩ => by
        change b = true at hb
        subst hb
        exact e.symm⟩
    · change z ∈ x ↔ ∃ b : HSet.twoCycle.{u}.Node, b.down = false ∧ d b = z
      rw [hx, HSet.mem_singleton]
      exact ⟨fun h => ⟨⟨false⟩, rfl, h.symm⟩, fun ⟨⟨b⟩, hb, e⟩ => by
        change b = false at hb
        subst hb
        exact e.symm⟩
  have hxΩ : x = HSet.quineAtom :=
    (congrFun hd.eq_decorate ⟨true⟩).trans (HSet.decorate_twoCycle _)
  have hyΩ : y = HSet.quineAtom :=
    (congrFun hd.eq_decorate ⟨false⟩).trans (HSet.decorate_twoCycle _)
  rw [hxΩ, hyΩ]

/-- No two distinct hypersets are each the other's singleton. -/
theorem not_exists_distinct_singleton_pair :
    ¬ ∃ x y : HSet.{u}, x ≠ y ∧ x = {y} ∧ y = {x} :=
  fun ⟨_, _, ne, hx, hy⟩ => ne (eq_of_eq_singleton_of_eq_singleton hx hy)

/-! ## Decorations with one prescribed extra member per node -/

section Parameters

variable {α : Type u} (r : α → α → Prop) (t : α → HSet.{u})

/-- A new point over a chosen graph of each parameter. -/
noncomputable def paramGraph : AccessiblePointedGraph.{u} :=
  sup fun a => HSet.Presentation.choice.graph (t a)

/-- The node of the parameter graph that pictures the parameter of `a`. -/
noncomputable def paramNode (a : α) : (paramGraph t).Node :=
  some ⟨a, (HSet.Presentation.choice.graph (t a)).point⟩

/-- The edges of the graph `r` extended by the parameters: the edges of `r`, an edge from each
node to the picture of its parameter, and the edges of the parameter graph. -/
inductive WithEdge : α ⊕ (paramGraph t).Node → α ⊕ (paramGraph t).Node → Prop
  | node {a b : α} : r a b → WithEdge (.inl a) (.inl b)
  | param (a : α) : WithEdge (.inl a) (.inr (paramNode t a))
  | inner {n m : (paramGraph t).Node} : (paramGraph t).edge n m → WithEdge (.inr n) (.inr m)

/-- The decoration of `r` in which the node `a` has the extra member `t a`. -/
noncomputable def decorateWith (a : α) : HSet.{u} :=
  HSet.decorate (WithEdge r t) (.inl a)

theorem decorate_withEdge_inr (n : (paramGraph t).Node) :
    HSet.decorate (WithEdge r t) (.inr n) = HSet.decorate (paramGraph t).edge n := by
  refine (HSet.decorate_eq_of_bisimilar
    (bisimilar_apply (r := (paramGraph t).edge) (s := WithEdge r t) (f := Sum.inr)
      (fun _ _ h => .inner h) (fun n b h => ?_) n)).symm
  cases h with
  | inner h => exact ⟨_, h, rfl⟩

theorem decorate_paramNode (a : α) :
    HSet.decorate (paramGraph t).edge (paramNode t a) = t a :=
  (HSet.sound (repoint_sup_equiv (g := fun a => HSet.Presentation.choice.graph (t a)) a)).trans
    (HSet.Presentation.choice.mk_graph (t a))

/-- **The members of `decorateWith r t a` are the decorations of the children of `a`, and
`t a`.** -/
theorem mem_decorateWith {a : α} {y : HSet.{u}} :
    y ∈ decorateWith r t a ↔ (∃ b, r a b ∧ decorateWith r t b = y) ∨ y = t a := by
  rw [decorateWith, HSet.mem_decorate]
  constructor
  · rintro ⟨c, hc, rfl⟩
    cases hc with
    | node h => exact Or.inl ⟨_, h, rfl⟩
    | param => exact Or.inr (by rw [decorate_withEdge_inr, decorate_paramNode])
  · rintro (⟨b, hb, rfl⟩ | rfl)
    · exact ⟨_, .node hb, rfl⟩
    · exact ⟨_, .param a, by rw [decorate_withEdge_inr, decorate_paramNode]⟩

end Parameters

/-! ## The anti-founded universe hosts every graph -/

/-- The tag `{Ω, s}`. -/
def tag (s : HSet.{u}) : HSet.{u} :=
  {HSet.quineAtom, s}

theorem not_wf_tag (s : HSet.{u}) : ¬ (tag s).WF :=
  HSet.not_wf_of_mem (HSet.mem_pair.mpr (Or.inl rfl)) HSet.not_wf_quineAtom

/-- A tag with a well-founded name is not `Ω`. -/
theorem tag_ne_quineAtom {s : HSet.{u}} (hs : s.WF) : tag s ≠ HSet.quineAtom := by
  intro equal
  have member : s ∈ tag s := HSet.mem_pair.mpr (Or.inr rfl)
  rw [equal, HSet.mem_quineAtom] at member
  exact HSet.not_wf_quineAtom (member ▸ hs)

/-- Tags with well-founded names are equal only when the names are. -/
theorem tag_injective {s s' : HSet.{u}} (hs : s.WF) (equal : tag s = tag s') : s = s' := by
  have member : s ∈ tag s' := equal ▸ HSet.mem_pair.mpr (Or.inr rfl)
  rcases HSet.mem_pair.mp member with h | h
  · exact absurd (h ▸ hs) HSet.not_wf_quineAtom
  · exact h

/-- A well-founded name for each element of a type of the lower level. -/
noncomputable def nodeName {α : Type u} (a : α) : HSet.{u} :=
  HSet.ofZFSet ((Ordinal.typein (WellOrderingRel (α := α))).toRelEmbedding a).toZFSet

theorem nodeName_wf {α : Type u} (a : α) : (nodeName a).WF :=
  HSet.wf_ofZFSet _

theorem nodeName_injective {α : Type u} : Function.Injective (nodeName (α := α)) :=
  fun _ _ equal => Ordinal.typein_injective _
    (Ordinal.toZFSet_injective (HSet.ofZFSet_injective equal))

/-- **Every graph on a type of the lower level is hosted by the hypersets**, with membership
kept and reflected. -/
theorem exists_membership_embedding {α : Type u} (r : α → α → Prop) :
    ∃ f : α → HSet.{u}, Function.Injective f ∧ ∀ a b, f b ∈ f a ↔ r a b := by
  let t : α → HSet.{u} := fun a => tag (nodeName a)
  let f := decorateWith r t
  have tag_mem : ∀ a, t a ∈ f a := fun a => (mem_decorateWith r t).mpr (Or.inr rfl)
  have not_tag : ∀ a c, f a ≠ t c := by
    intro a c equal
    have member : t a ∈ t c := equal ▸ tag_mem a
    rcases HSet.mem_pair.mp member with h | h
    · exact tag_ne_quineAtom (nodeName_wf a) h
    · exact not_wf_tag _ (h ▸ nodeName_wf c)
  have injective : Function.Injective f := by
    intro a b equal
    have member : t a ∈ f b := equal ▸ tag_mem a
    rcases (mem_decorateWith r t).mp member with ⟨c, _, h⟩ | h
    · exact absurd h (not_tag c a)
    · exact nodeName_injective (tag_injective (nodeName_wf a) h)
  refine ⟨f, injective, fun a b => ?_⟩
  rw [mem_decorateWith]
  constructor
  · rintro (⟨c, hc, h⟩ | h)
    · exact injective h ▸ hc
    · exact absurd h (not_tag b a)
  · exact fun h => Or.inl ⟨b, h, rfl⟩

/-- **The two-node cycle, hosted with tags**: two distinct hypersets, each a member of the
other and neither a member of itself. -/
theorem exists_tagged_twoCycle :
    ∃ x y : HSet.{u}, x ≠ y ∧ x ∈ y ∧ y ∈ x ∧ x ∉ x ∧ y ∉ y := by
  obtain ⟨f, injective, hf⟩ := exists_membership_embedding HSet.twoCycle.{u}.edge
  refine ⟨f ⟨true⟩, f ⟨false⟩, fun h => Bool.noConfusion (congrArg ULift.down (injective h)),
    (hf _ _).mpr rfl, (hf _ _).mpr rfl, fun h => ?_, fun h => ?_⟩
  · exact Bool.noConfusion ((hf ⟨true⟩ ⟨true⟩).mp h)
  · exact Bool.noConfusion ((hf ⟨false⟩ ⟨false⟩).mp h)

/-! ## The well-founded sets host exactly well-founded graphs -/

/-- **A membership-keeping map into `ZFSet` makes the child relation well-founded.** -/
theorem wellFounded_of_zfset_embedding {α : Type*} {r : α → α → Prop} {f : α → ZFSet.{u}}
    (hf : ∀ a b, f b ∈ f a ↔ r a b) : WellFounded fun b a => r a b :=
  Subrelation.wf (fun {b a} h => (hf a b).mpr h) (InvImage.wf f ZFSet.mem_wf)

/-- The one-node loop has no membership-keeping map into `ZFSet`. -/
theorem not_exists_zfset_embedding_loop :
    ¬ ∃ f : HSet.loop.{u}.Node → ZFSet.{u}, ∀ a b, f b ∈ f a ↔ HSet.loop.edge a b := by
  rintro ⟨f, hf⟩
  exact ZFSet.mem_irrefl _ ((hf PUnit.unit PUnit.unit).mpr trivial)

/-- The hypersets host the one-node loop. -/
example : ∃ f : HSet.loop.{u}.Node → HSet.{u}, Function.Injective f ∧
    ∀ a b, f b ∈ f a ↔ HSet.loop.edge a b :=
  exists_membership_embedding _

/-! ## The two maximal admitted theories in one carrier -/

/-- **The plural family in one carrier.** The hypersets satisfy exactly the anti-founded
theory, and their well-founded part, with membership restricted, satisfies the well-founded
theory. -/
theorem plural_family_in_one_carrier :
    (∀ p, p.Holds (fun x y : HSet.{u} => x ∈ y) ↔ p ∈ antiFounded) ∧
      ∀ p ∈ wellFounded, p.Holds (bubbleMem (fun x y : HSet.{u} => x ∈ y)) :=
  ⟨hypersets_holds_iff, bubble_wellFounded fun p hp =>
    (hypersets_holds_iff p).mpr (Set.mem_insert_of_mem _ hp)⟩

#print axioms exists_injective_decoration_iff
#print axioms not_exists_injective_decoration_twoCycle
#print axioms eq_of_eq_singleton_of_eq_singleton
#print axioms mem_decorateWith
#print axioms exists_membership_embedding
#print axioms exists_tagged_twoCycle
#print axioms wellFounded_of_zfset_embedding
#print axioms plural_family_in_one_carrier

end Mettapedia.SetTheory.OpenTower.AntiFounded
