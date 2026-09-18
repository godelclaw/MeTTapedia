import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
# Fibrations of reconfiguration systems

A *reconfiguration system* is a type of states with a one-step move relation;
reachability is the reflexive-transitive closure `Relation.ReflTransGen`.

This file isolates the one mechanism by which connectivity passes from a
coarse system to a finer one.  A projection `proj : Total → Base` is a
*fibration* when

* its fibres are connected: two states with the same projection are joined by
  a path of total moves; and
* it lifts steps: whenever the projection of a total state takes one base move,
  some total path starting at that state ends over the new base state.

Then every base path lifts to a total path from any chosen start, and so base
connectivity gives total connectivity.  Surjectivity of the projection plays no
part in this; it is needed only where one wants to lift a *target* rather than a
path (see `Completability`).

The same statement also holds fibrewise over a labelling of the base: if the
base is connected within each label class, the total system is connected
within each label class of the composite labelling.  This relative form is the
shape of "local Kempe reachability with fixed input", where the label is the
input boundary word.
-/

namespace Mettapedia.Combinatorics.Reconfiguration

open Relation

universe u v w

section Basic

variable {α : Type u} {β : Type v} (step : α → α → Prop)

/-- Every state reaches every state. -/
def Connected : Prop :=
  ∀ x y, ReflTransGen step x y

/-- States carrying the same label reach one another. -/
def FibresConnected (label : α → β) : Prop :=
  ∀ x y, label x = label y → ReflTransGen step x y

variable {step}

/-- Connectivity is fibre connectivity for a constant label. -/
theorem connected_iff_fibresConnected_const :
    Connected step ↔ FibresConnected step (fun _ : α => ()) :=
  ⟨fun h x y _ => h x y, fun h x y => h x y rfl⟩

theorem Connected.fibresConnected (h : Connected step) (label : α → β) :
    FibresConnected step label :=
  fun x y _ => h x y

/-- A finer labelling has connected fibres whenever a coarser one does. -/
theorem FibresConnected.of_comp {γ : Type w} {label : α → β} (f : β → γ)
    (h : FibresConnected step (f ∘ label)) : FibresConnected step label :=
  fun x y hxy => h x y (congrArg f hxy)

/-- Fibre connectivity transfers to any labelling whose classes refine those of
a labelling with connected fibres. -/
theorem FibresConnected.of_imp {γ : Type w} {label : α → β} {label' : α → γ}
    (himp : ∀ x y, label x = label y → label' x = label' y)
    (h : FibresConnected step label') : FibresConnected step label :=
  fun x y hxy => h x y (himp x y hxy)

theorem FibresConnected.mono {step' : α → α → Prop}
    (hle : ∀ x y, step x y → step' x y) {label : α → β}
    (h : FibresConnected step label) : FibresConnected step' label :=
  fun x y hxy => (h x y hxy).mono hle

theorem Connected.mono {step' : α → α → Prop}
    (hle : ∀ x y, step x y → step' x y) (h : Connected step) :
    Connected step' :=
  fun x y => (h x y).mono hle

/-- Paths inside an invariant set.  If moves never leave a set `S`, then paths
of the move relation restricted to `S` are exactly the paths of the move
relation between members of `S`. -/
theorem reflTransGen_subtype_iff {S : α → Prop}
    (hclosed : ∀ x y, S x → step x y → S y) (x y : Subtype S) :
    ReflTransGen (fun a b : Subtype S => step a.1 b.1) x y ↔ ReflTransGen step x.1 y.1 := by
  constructor
  · intro h
    exact ReflTransGen.lift Subtype.val (fun _ _ hab => hab) h
  · intro h
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    change ReflTransGen step x y at h
    have key : ∀ z, ReflTransGen step x z → ∃ hz : S z,
        ReflTransGen (fun a b : Subtype S => step a.1 b.1) ⟨x, hx⟩ ⟨z, hz⟩ := by
      intro z hxz
      induction hxz with
      | refl => exact ⟨hx, ReflTransGen.refl⟩
      | tail _ hstep ih =>
          obtain ⟨hw, hpath⟩ := ih
          exact ⟨hclosed _ _ hw hstep, hpath.tail hstep⟩
    obtain ⟨_, hpath⟩ := key y h
    exact hpath

end Basic

section Lifting

variable {Total : Type u} {Base : Type v}
  (totalStep : Total → Total → Prop) (baseStep : Base → Base → Prop)
  (proj : Total → Base)

/-- **Step lifting.**  Each base move out of the projection of a total state is
realised by a total path from that state ending over the move's target. -/
def LiftsSteps : Prop :=
  ∀ x b, baseStep (proj x) b → ∃ y, proj y = b ∧ ReflTransGen totalStep x y

/-- **Fibration.**  Connected fibres and step lifting. -/
structure Fibration : Prop where
  fibresConnected : FibresConnected totalStep proj
  liftsSteps : LiftsSteps totalStep baseStep proj

/-- Total moves project to base paths.  This is the converse direction to
lifting, used to transport connectivity downwards. -/
def ProjectsSteps : Prop :=
  ∀ x y, totalStep x y → ReflTransGen baseStep (proj x) (proj y)

variable {totalStep baseStep proj}

/-- Lifting only needs the base moves actually used. -/
theorem LiftsSteps.mono {baseStep' : Base → Base → Prop}
    (hle : ∀ b b', baseStep' b b' → baseStep b b')
    (h : LiftsSteps totalStep baseStep proj) :
    LiftsSteps totalStep baseStep' proj :=
  fun x b hb => h x b (hle _ _ hb)

/-- **Path lifting.**  A base path from the projection of `x` lifts to a total
path from `x` ending over the path's endpoint. -/
theorem LiftsSteps.lift (h : LiftsSteps totalStep baseStep proj)
    {x : Total} {b : Base} (hpath : ReflTransGen baseStep (proj x) b) :
    ∃ y, proj y = b ∧ ReflTransGen totalStep x y := by
  induction hpath with
  | refl => exact ⟨x, rfl, ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨y, hy, hxy⟩ := ih
      obtain ⟨z, hz, hyz⟩ := h y _ (hy ▸ hstep)
      exact ⟨z, hz, hxy.trans hyz⟩

/-- Along a lifted path every base state visited is a projection: step lifting
confines base paths from projections to the image of `proj`. -/
theorem LiftsSteps.exists_proj_eq (h : LiftsSteps totalStep baseStep proj)
    {x : Total} {b : Base} (hpath : ReflTransGen baseStep (proj x) b) :
    ∃ y, proj y = b :=
  (h.lift hpath).imp fun _ hy => hy.1

/-- A base path between two projections lifts to a total path between the two
chosen states. -/
theorem Fibration.reach (h : Fibration totalStep baseStep proj) {x y : Total}
    (hpath : ReflTransGen baseStep (proj x) (proj y)) :
    ReflTransGen totalStep x y := by
  obtain ⟨z, hz, hxz⟩ := h.liftsSteps.lift hpath
  exact hxz.trans (h.fibresConnected z y hz)

/-- **Fibration theorem.**  Base connectivity lifts to total connectivity. -/
theorem Fibration.connected (h : Fibration totalStep baseStep proj)
    (hbase : Connected baseStep) : Connected totalStep :=
  fun x y => h.reach (hbase (proj x) (proj y))

/-- **Relative fibration theorem.**  Fibre connectivity of the base over a
labelling lifts to fibre connectivity of the total system over the composite
labelling. -/
theorem Fibration.fibresConnected_comp {γ : Type w}
    (h : Fibration totalStep baseStep proj) {label : Base → γ}
    (hbase : FibresConnected baseStep label) :
    FibresConnected totalStep (label ∘ proj) :=
  fun x y hxy => h.reach (hbase (proj x) (proj y) hxy)

/-- **Fibrations compose.**  A fibration over a fibration is a fibration over
the bottom: this is the iterated form, one interface at a time. -/
theorem Fibration.comp {Mid : Type w} {midStep : Mid → Mid → Prop}
    {upper : Total → Mid} {lower : Mid → Base}
    (hupper : Fibration totalStep midStep upper)
    (hlower : Fibration midStep baseStep lower) :
    Fibration totalStep baseStep (lower ∘ upper) where
  fibresConnected x y hxy := hupper.reach (hlower.fibresConnected _ _ hxy)
  liftsSteps x b hb := by
    obtain ⟨m, hm, hpath⟩ := hlower.liftsSteps (upper x) b hb
    obtain ⟨y, hy, hxy⟩ := hupper.liftsSteps.lift hpath
    exact ⟨y, by simp [hy, hm], hxy⟩

/-- Projected paths: a total path projects to a base path. -/
theorem ProjectsSteps.reach (h : ProjectsSteps totalStep baseStep proj)
    {x y : Total} (hpath : ReflTransGen totalStep x y) :
    ReflTransGen baseStep (proj x) (proj y) := by
  induction hpath with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (h _ _ hstep)

/-- Connectivity descends along a surjective projection whose moves project to
paths. -/
theorem ProjectsSteps.connected (h : ProjectsSteps totalStep baseStep proj)
    (hsurj : Function.Surjective proj) (htotal : Connected totalStep) :
    Connected baseStep := by
  intro a b
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  exact h.reach (htotal x y)

end Lifting

end Mettapedia.Combinatorics.Reconfiguration
