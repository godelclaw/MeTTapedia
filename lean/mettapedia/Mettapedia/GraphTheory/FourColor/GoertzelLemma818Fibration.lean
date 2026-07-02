namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: abstract fibration connectivity

This module contains the reusable graph-theoretic core for the frontier-state
composition plan.  It is deliberately independent of the particular
`tau`/mirror-`tau` tables: once a concrete chain proof supplies connected
fibers and lifted base moves, connectedness of the total graph follows from
connectedness of the base graph.
-/

namespace GoertzelLemma818Fibration

universe u v

/-- Reflexive transitive reachability for a directed step relation. -/
inductive Reach {α : Type u} (step : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Reach step x x
  | tail {x y z : α} : Reach step x y → step y z → Reach step x z

namespace Reach

variable {α : Type u} {step : α → α → Prop}

theorem single {x y : α} (hxy : step x y) : Reach step x y :=
  Reach.tail (Reach.refl x) hxy

theorem trans {x y z : α}
    (hxy : Reach step x y) (hyz : Reach step y z) :
    Reach step x z := by
  induction hyz with
  | refl =>
      exact hxy
  | tail hyw hwz ih =>
      exact Reach.tail ih hwz

theorem map
    {β : Type v} {stepβ : β → β → Prop} {f : α → β}
    (hmap : ∀ {x y : α}, step x y → stepβ (f x) (f y))
    {x y : α} (hxy : Reach step x y) :
    Reach stepβ (f x) (f y) := by
  induction hxy with
  | refl =>
      exact Reach.refl (f x)
  | tail hpre hstep ih =>
      exact Reach.tail ih (hmap hstep)

theorem reverse_of_stepSymmetric
    (hsym : ∀ {x y : α}, step x y → step y x)
    {x y : α} (hxy : Reach step x y) :
    Reach step y x := by
  induction hxy with
  | refl =>
      exact Reach.refl x
  | tail hpre hstep ih =>
      exact Reach.trans (Reach.single (hsym hstep)) ih

end Reach

/-- A step relation is connected when every ordered pair is reachable. -/
def Connected {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ x y, Reach step x y

/-- A step relation is symmetric when every directed step can be reversed. -/
def StepSymmetric {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ {x y}, step x y → step y x

/--
A rooted connectivity certificate for a directed step relation.

Generated finite checks often produce this shape directly: every node can reach
a chosen root and the root can reach every node.
-/
structure RootedConnectedCertificate
    {α : Type u} (step : α → α → Prop) : Type u where
  root : α
  reachFromRoot : ∀ x, Reach step root x
  reachToRoot : ∀ x, Reach step x root

namespace RootedConnectedCertificate

variable {α : Type u} {step : α → α → Prop}

theorem connected (cert : RootedConnectedCertificate step) :
    Connected step := by
  intro x y
  exact Reach.trans (cert.reachToRoot x) (cert.reachFromRoot y)

end RootedConnectedCertificate

theorem connected_of_root_reachable_and_stepSymmetric
    {α : Type u} {step : α → α → Prop}
    (hsym : StepSymmetric step)
    (root : α)
    (hroot : ∀ x, Reach step x root) :
    Connected step := by
  intro x y
  exact Reach.trans (hroot x)
    (Reach.reverse_of_stepSymmetric hsym (hroot y))

/--
Data needed to lift base connectivity to total connectivity.

`fiberReach` connects points in the same fiber of `proj`; `liftStep` says every
one-step base move out of the projection of a total point can be realized by a
path in the total graph ending over the requested base point.
-/
structure Fibration
    {Total : Type u} {Base : Type v}
    (totalStep : Total → Total → Prop)
    (baseStep : Base → Base → Prop)
    (proj : Total → Base) : Prop where
  fiberReach :
    ∀ x y : Total, proj x = proj y → Reach totalStep x y
  liftStep :
    ∀ (x : Total) (b : Base), baseStep (proj x) b →
      ∃ y : Total, proj y = b ∧ Reach totalStep x y

namespace Fibration

variable {Total : Type u} {Base : Type v}
variable {totalStep : Total → Total → Prop}
variable {baseStep : Base → Base → Prop}
variable {proj : Total → Base}

theorem exists_reachable_over_base
    (h : Fibration totalStep baseStep proj)
    {x : Total} {b : Base}
    (hbase : Reach baseStep (proj x) b) :
    ∃ y : Total, proj y = b ∧ Reach totalStep x y := by
  induction hbase with
  | refl =>
      exact ⟨x, rfl, Reach.refl x⟩
  | tail hpre hstep ih =>
      rcases ih with ⟨z, hz, hxz⟩
      case tail bMid bNext =>
        have hstep' : baseStep (proj z) bNext := by
          simpa [hz] using hstep
        rcases h.liftStep z bNext hstep' with ⟨w, hw, hzw⟩
        exact ⟨w, hw, Reach.trans hxz hzw⟩

theorem totalReach_of_baseReach
    (h : Fibration totalStep baseStep proj)
    {x y : Total}
    (hbase : Reach baseStep (proj x) (proj y)) :
    Reach totalStep x y := by
  rcases h.exists_reachable_over_base hbase with ⟨z, hz, hxz⟩
  exact Reach.trans hxz (h.fiberReach z y hz)

theorem totalConnected_of_baseConnected
    (h : Fibration totalStep baseStep proj)
    (hbase : Connected baseStep) :
    Connected totalStep := by
  intro x y
  exact h.totalReach_of_baseReach (hbase (proj x) (proj y))

end Fibration

end GoertzelLemma818Fibration

end Mettapedia.GraphTheory.FourColor
