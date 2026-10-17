import Mettapedia.Languages.MeTTa.LayerEffects

/-!
# The speculative readout is an observer of ordered runs

`LayerEffects.Spec K C W X = W → Ans K (X × W × C)` is an answer readout: it
aggregates equal outcomes, forgets their order and drops branches that return
no answer, with the cost those branches paid.  This module states the
operational side it reads and proves the readout is an observer of it.

An **ordered run** returns the list of its branch outcomes in order
(`Ordered`).  A branch that fails keeps its world and the cost it paid.
Sequencing runs the continuation on each successful branch, in order, and
passes failed branches through (`Ordered.bind`).

* **The readout is a monad morphism** (`observe_pure`, `observe_bind`):
  observing a sequenced run is sequencing the observations in `Spec ℕ`, with
  each successful branch's cost charged to its continuation.  So every law of
  `Spec` proved on readouts is a law about what ordered runs show through this
  observer, and nothing more.
* **It forgets order** (`Controls.observe_forgets_order`) **and failed work**
  (`Controls.observe_forgets_failed_cost`): two runs that differ in the order of
  their branches, or in the cost of a failed branch, have the same readout.
  Claims about order or paid work belong to the ordered runs and to the run
  accounts, not to `Spec`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpecRunObserver

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.LayerEffects

universe u v

variable {C : Type u} [CommMonoid C] {W : Type v} {X Y : Type*}

/-- **Ordered runs**: branch outcomes in order; a failed branch keeps its world
and the cost it paid. -/
abbrev Ordered (C : Type u) (W : Type v) (X : Type*) := W → List (Option X × W × C)

namespace Ordered

/-- One successful branch at no cost. -/
def pure (x : X) : Ordered C W X := fun world => [(some x, world, 1)]

/-- Continue one branch: run the continuation on a success and charge the
branch's cost; pass a failure through. -/
def continueBranch (f : X → Ordered C W Y) : Option X × W × C → List (Option Y × W × C)
  | (some x, world, cost) => (f x world).map fun result => (result.1, result.2.1, cost * result.2.2)
  | (none, world, cost) => [(none, world, cost)]

/-- Sequencing, branch by branch, in order. -/
def bind (m : Ordered C W X) (f : X → Ordered C W Y) : Ordered C W Y :=
  fun world => (m world).flatMap (continueBranch f)

end Ordered

/-- **The readout of a list of outcomes**: count each successful outcome. -/
noncomputable def observe : List (Option X × W × C) → Ans ℕ (X × W × C)
  | [] => 0
  | (some x, world, cost) :: rest => Finsupp.single (x, world, cost) 1 + observe rest
  | (none, _, _) :: rest => observe rest

omit [CommMonoid C] in
theorem observe_append (first second : List (Option X × W × C)) :
    observe (first ++ second) = observe first + observe second := by
  induction first with
  | nil => simp [observe]
  | cons head rest ih =>
      obtain ⟨value, world, cost⟩ := head
      cases value <;> simp [observe, ih, add_assoc]

theorem observe_map_charge (cost : C) (outcomes : List (Option Y × W × C)) :
    observe (outcomes.map fun result => (result.1, result.2.1, cost * result.2.2)) =
      Spec.charge cost (observe outcomes) := by
  induction outcomes with
  | nil =>
      simp only [List.map_nil, observe, Spec.charge, Ans.map_eq_mapDomain, Finsupp.mapDomain_zero]
  | cons head rest ih =>
      obtain ⟨value, world, c⟩ := head
      cases value with
      | none => simpa [observe] using ih
      | some y =>
          simp only [List.map_cons, observe]
          rw [ih, Spec.charge, Spec.charge, Ans.map_eq_mapDomain, Ans.map_eq_mapDomain,
            Finsupp.mapDomain_add, Finsupp.mapDomain_single]

/-- The observation of a run. -/
noncomputable def observeRun (m : Ordered C W X) : Spec ℕ C W X := fun world => observe (m world)

/-- **The readout preserves returns.** -/
theorem observe_pure (x : X) : observeRun (Ordered.pure x : Ordered C W X) = Spec.pure x := by
  funext world
  simp [observeRun, Ordered.pure, observe, Spec.pure, Ans.pure]

/-- **The readout is a monad morphism**: observing a sequenced run is sequencing
the observations. -/
theorem observe_bind (m : Ordered C W X) (f : X → Ordered C W Y) :
    observeRun (Ordered.bind m f) = Spec.bind (observeRun m) fun x => observeRun (f x) := by
  funext world
  simp only [observeRun, Ordered.bind, Spec.bind]
  induction m world with
  | nil => simp [observe]
  | cons head rest ih =>
      obtain ⟨value, w, cost⟩ := head
      rw [List.flatMap_cons, observe_append, ih]
      cases value with
      | none => simp [observe, Ordered.continueBranch]
      | some x =>
          simp only [observe, Ordered.continueBranch, Ans.add_bind, Ans.single_bind, one_smul]
          rw [observe_map_charge]

/-! ## Controls -/

namespace Controls

omit [CommMonoid C] in
/-- **The readout forgets order.** -/
theorem observe_forgets_order (first second : X × W × C) :
    observe [(some first.1, first.2.1, first.2.2), (some second.1, second.2.1, second.2.2)] =
      observe [(some second.1, second.2.1, second.2.2), (some first.1, first.2.1, first.2.2)] := by
  simp [observe, add_comm]

omit [CommMonoid C] in
/-- **The readout forgets the cost of failed branches.** -/
theorem observe_forgets_failed_cost (world : W) (cheap expensive : C) :
    observe ([(none, world, cheap)] : List (Option X × W × C)) =
      observe ([(none, world, expensive)] : List (Option X × W × C)) := rfl

end Controls

end Mettapedia.Languages.MeTTa.SpecRunObserver
