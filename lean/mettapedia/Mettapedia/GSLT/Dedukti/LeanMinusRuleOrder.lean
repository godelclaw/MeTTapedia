import Mettapedia.GSLT.Dedukti.LeanMinusPriority
import Mettapedia.GSLT.Distinction.ActionCommutation
import Mettapedia.GSLT.Causality.EventConcurrency

/-!
# Rule order, read as two events

While a universe-polymorphic declaration is checked and then used, two things
happen to a term that mentions a level parameter: the parameter is
**instantiated**, and the root of the term is contracted by the **first rule
that matches**.  `ordered_not_substitution_stable` says that the two do not
commute for the paper's rules tried in order, and
`orderedStep_iff_of_orthogonal` that the order of the rules does not matter
when no two rules overlap.  This module states both in the two existing
vocabularies of reordering.

## As actions on a state (`Distinction.ActionCommutation`)

`checkAct signature rules index replacement` acts on a term, or on nothing once
a selection has found no rule: `instantiate` substitutes `replacement` for the
variable `index`, and `select` applies `rootReduct`, the contraction of the
root by beta, by a definition or by the first rule of the list that matches.

* **The paper's rules** (`paper_select_instantiate_not_commute`): at `v x 0`
  both orders succeed, `select` then `instantiate` gives the code of a
  variable, `instantiate` then `select` gives `zero`, and the two
  endomorphisms do not commute in the monoid of endomorphisms of the state.
* **Commutation of total actions is the wrong statement for the positive
  half** (`frozen_select_instantiate_not_commute`): on the frozen rules, which
  do not overlap, the two endomorphisms do not commute either.  At `v x 0` no
  rule matches; after the instantiation one does.  A substitution creates
  redexes, so "stable under substitution" is one inclusion of composites, and
  `Commute` asks for an equality.

## As independent events (`Causality.EventConcurrency`)

`checkPresentation signature rules index replacement` presents the two events
as the sites of a theory whose steps are the instantiation of one variable and
the ordered steps (`OrderedStep`, closed under contexts).  Independence of two
enabled events with residuals (`Concurrency`) is a statement about the terms at
which both are enabled, which is what stability under substitution is.

* **No two rules overlap** (`orthogonalConcurrency`): the instantiation and
  every ordered step are independent events.  The residual of the step after
  the instantiation is the step of the instance
  (`orderedStep_subst_of_orthogonal`), and the two routes meet.
* **The paper's rules** (`paper_fallback_not_independent`): in no concurrency on
  the presentation are the instantiation of `x` and the fallback step at
  `v x 0` independent: the residual of the fallback would be the step that
  `ordered_not_substitution_stable` refutes.

`Distinction.HistoryIndependence.Concurrent` is the independence of the four
events of the history grammar on multisets of nodes, defined by what each
event consumes, reads and produces; a substitution and a selection act on one
term and have no such reading.  The notion used here is the one that module
instantiates, `EventConcurrency.Concurrency`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig subst subst0)
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.EventConcurrency
open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving (run)
open Mettapedia.GSLT.Distinction.ActionCommutation (endo forall_comm_iff_commute)

/-! ## The two events -/

/-- The two events on a term of a declaration: its level parameter is
instantiated, or its root is contracted by the first rule that matches. -/
inductive CheckEvent where
  | instantiate
  | select
  deriving DecidableEq, Repr

/-! ## As actions on a state -/

/-- **The action of the two events** on a term, or on nothing once a selection
has found no rule: `instantiate` substitutes `replacement` for the variable
`index`, and `select` contracts the root by beta, by a definition, or by the
first rule of the list that matches. -/
def checkAct (signature : Sig) (rules : List RewriteRule) (index : Nat) (replacement : Term) :
    Option Term → CheckEvent → Option Term
  | state, .instantiate => state.map (subst index replacement)
  | state, .select => state.bind (rootReduct signature rules)

/-- **Instantiating a level parameter and selecting the first matching rule do
not commute, for the paper's rules.**  At `v x 0` both orders succeed:
selecting first gives the code of a variable, by the fallback; instantiating
`x` by `inst zero` first gives `zero`, by the first rule on `v`. -/
theorem paper_select_instantiate_not_commute :
    run (checkAct leanSig leanRules 0 (instOf zero)) (some (ap "v" [.var 0, zeroN]))
        [.select, .instantiate] = some (levelVariable zeroN) ∧
      run (checkAct leanSig leanRules 0 (instOf zero)) (some (ap "v" [.var 0, zeroN]))
        [.instantiate, .select] = some zero ∧
      ¬ Commute (endo (checkAct leanSig leanRules 0 (instOf zero)) .select)
        (endo (checkAct leanSig leanRules 0 (instOf zero)) .instantiate) := by
  refine ⟨by decide +kernel, by decide +kernel, fun commute => ?_⟩
  exact absurd ((forall_comm_iff_commute _ _ _).mpr commute (some (ap "v" [.var 0, zeroN])))
    (by decide +kernel)

/-- **The two actions do not commute on rules that do not overlap either**: on
the frozen rules no rule matches `v x 0`, and after the instantiation of `x`
by `inst zero` the first rule on `v` does.  A substitution creates redexes. -/
theorem frozen_select_instantiate_not_commute :
    run (checkAct frozenSig frozenRules 0 (instOf zero)) (some (ap "v" [.var 0, zeroN]))
        [.select, .instantiate] = none ∧
      run (checkAct frozenSig frozenRules 0 (instOf zero)) (some (ap "v" [.var 0, zeroN]))
        [.instantiate, .select] = some zero ∧
      ¬ Commute (endo (checkAct frozenSig frozenRules 0 (instOf zero)) .select)
        (endo (checkAct frozenSig frozenRules 0 (instOf zero)) .instantiate) := by
  refine ⟨by decide +kernel, by decide +kernel, fun commute => ?_⟩
  exact absurd ((forall_comm_iff_commute _ _ _).mpr commute (some (ap "v" [.var 0, zeroN])))
    (by decide +kernel)

/-! ## As independent events -/

/-- **One of the two events fires**: the instantiation of the variable `index`
by `replacement`, or a step of the rules tried in order. -/
inductive Fires (signature : Sig) (rules : List RewriteRule) (index : Nat) (replacement : Term) :
    CheckEvent → Term → Term → Prop where
  | instantiate (source : Term) :
      Fires signature rules index replacement .instantiate source (subst index replacement source)
  | select {source target : Term} :
      OrderedStep signature rules source target →
        Fires signature rules index replacement .select source target

section Events

variable {signature : Sig} {rules : List RewriteRule} {index : Nat} {replacement : Term}

theorem Fires.ordered {source target : Term}
    (fires : Fires signature rules index replacement .select source target) :
    OrderedStep signature rules source target := by
  cases fires with
  | select step => exact step

theorem Fires.substituted {source target : Term}
    (fires : Fires signature rules index replacement .instantiate source target) :
    target = subst index replacement source := by
  cases fires
  rfl

end Events

/-- The terms, with the two events as steps. -/
def checkTheory (signature : Sig) (rules : List RewriteRule) (index : Nat) (replacement : Term) :
    GSLT where
  Term := Term
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun source target => ∃ event, Fires signature rules index replacement event source target
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **The two events as the sites of a presentation.** -/
def checkPresentation (signature : Sig) (rules : List RewriteRule) (index : Nat) (replacement : Term) :
    InteractionPresentation (checkTheory signature rules index replacement) where
  Site := CheckEvent
  Event := fun event source target => PLift (Fires signature rules index replacement event source target)
  sound := fun evidence => ⟨_, evidence.down⟩

section Presented

variable {signature : Sig} {rules : List RewriteRule} {index : Nat} {replacement : Term}

/-- The instantiation, as an event enabled at every term. -/
def instantiateAt (signature : Sig) (rules : List RewriteRule) (index : Nat) (replacement : Term)
    (source : Term) : (checkPresentation signature rules index replacement).Enabled source where
  site := .instantiate
  target := subst index replacement source
  evidence := ⟨.instantiate source⟩

/-- A step of the rules tried in order, as an enabled event. -/
def selectAt (index : Nat) (replacement : Term) {source target : Term}
    (step : OrderedStep signature rules source target) :
    (checkPresentation signature rules index replacement).Enabled source where
  site := .select
  target := target
  evidence := ⟨.select step⟩

/-- **The independence of the two events, for an ordered relation that is
stable under the substitution**: an instantiation and an ordered step are
independent.  The residual of the step after the instantiation is the step of
the instance; the residual of the instantiation after the step is the
instantiation of the reduct. -/
def stableConcurrency
    (stable : ∀ {source target : Term}, OrderedStep signature rules source target →
      OrderedStep signature rules (subst index replacement source) (subst index replacement target)) :
    Concurrency (checkPresentation signature rules index replacement) where
  Independent := fun first second => first.site ≠ second.site
  symm := fun distinct => Ne.symm distinct
  residual := fun {source first second} distinct =>
    { site := second.site
      target :=
        match second.site with
        | .instantiate => subst index replacement first.target
        | .select => subst index replacement second.target
      evidence := ⟨by
        obtain ⟨firstSite, firstTarget, ⟨firstFires⟩⟩ := first
        obtain ⟨secondSite, secondTarget, ⟨secondFires⟩⟩ := second
        cases secondFires with
        | instantiate => exact .instantiate firstTarget
        | select step =>
            cases firstFires with
            | instantiate => exact .select (stable step)
            | select _ => exact absurd rfl distinct⟩ }
  residual_site := fun _ => rfl
  close := fun {source first second} distinct => by
    obtain ⟨firstSite, firstTarget, ⟨firstFires⟩⟩ := first
    obtain ⟨secondSite, secondTarget, ⟨secondFires⟩⟩ := second
    cases firstFires with
    | instantiate =>
        cases secondFires with
        | instantiate => exact absurd rfl distinct
        | select _ => rfl
    | select _ =>
        cases secondFires with
        | instantiate => rfl
        | select _ => exact absurd rfl distinct

/-- **The ordered steps of a list of rules that do not overlap are stable under
substitution.** -/
theorem orderedStep_subst_of_orthogonal (orthogonal : (Theory.ofSig signature rules).Orthogonal)
    {source target : Term} (step : OrderedStep signature rules source target) (index : Nat)
    (replacement : Term) :
    OrderedStep signature rules (subst index replacement source) (subst index replacement target) :=
  (orderedStep_iff_of_orthogonal orthogonal).mpr
    (((orderedStep_iff_of_orthogonal orthogonal).mp step).subst orthogonal.closedBodies index
      replacement)

/-- **When no two rules overlap, instantiating a variable and selecting the
first matching rule are independent events.** -/
def orthogonalConcurrency (orthogonal : (Theory.ofSig signature rules).Orthogonal) (index : Nat)
    (replacement : Term) : Concurrency (checkPresentation signature rules index replacement) :=
  stableConcurrency fun step => orderedStep_subst_of_orthogonal orthogonal step index replacement

end Presented

/-- **For the paper's rules, the instantiation of a level parameter and the
fallback step are independent in no concurrency.**  At `v x 0`, with `x`
instantiated by `inst zero`: the residual of the fallback step after the
instantiation would be an ordered step from `v (inst zero) 0` to the code of a
variable, which `ordered_not_substitution_stable` refutes. -/
theorem paper_fallback_not_independent
    (concurrency : Concurrency (checkPresentation leanSig leanRules 0 (instOf zero))) :
    ¬ concurrency.Independent
        (instantiateAt leanSig leanRules 0 (instOf zero) (ap "v" [.var 0, zeroN]))
        (selectAt 0 (instOf zero) ordered_not_substitution_stable.1) := by
  intro independent
  have selectSite := concurrency.residual_site independent
  have selectFires := (concurrency.residual independent).evidence.down
  rw [selectSite] at selectFires
  have instantiateSite := concurrency.residual_site (concurrency.symm independent)
  have instantiateFires := (concurrency.residual (concurrency.symm independent)).evidence.down
  rw [instantiateSite] at instantiateFires
  have step := Fires.ordered selectFires
  rw [concurrency.close independent, Fires.substituted instantiateFires] at step
  exact ordered_not_substitution_stable.2 step

#print axioms paper_select_instantiate_not_commute
#print axioms frozen_select_instantiate_not_commute
#print axioms stableConcurrency
#print axioms orderedStep_subst_of_orthogonal
#print axioms orthogonalConcurrency
#print axioms paper_fallback_not_independent

end Mettapedia.GSLT.Dedukti.LeanMinus
