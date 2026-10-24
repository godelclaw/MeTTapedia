import Mettapedia.OSLF.Framework.FiniteModels

/-!
# Finite-model certificates for steps inside contexts

A language declares where steps may happen inside a term: congruence sites, each a constructor label,
its number of arguments and the position that may step (`Site`). A step inside a context is a root
step, or a step of the argument at a declared site (`ContextStep`).

A certificate covers these steps when every declared site's operation respects the preorder: moving
the argument at that position down moves the whole term down (`Certificate.sitesCheck`, a finite
check over the carrier). Then every step in a context goes down the preorder (`contextStep_below`), and
a state from which no goal element lies below cannot reach the goals through scoped states, now with
steps anywhere the language allows (`cannotReachInContexts_of_check`). Steps under binders are not
among them: a value moved under extra binders by an unscoped instantiation would read the wrong ones.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FiniteModels

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal)

/-- A congruence site: a constructor label, its number of arguments, and the position that may step. -/
abbrev Site := String × ℕ × ℕ

/-- **A step inside a context**: a root step, or a step of the argument at a declared site. -/
inductive ContextStep (language : LanguageDef) (sites : List Site) : Pattern → Pattern → Prop where
  | root {source target : Pattern} : target ∈ rootReducts language source → ContextStep language sites source target
  | inside {label : String} {before after : List Pattern} {argument argument' : Pattern} :
      (label, before.length + after.length + 1, before.length) ∈ sites →
      ContextStep language sites argument argument' →
      ContextStep language sites (.apply label (before ++ argument :: after)) (.apply label (before ++ argument' :: after))

/-- The steps of a language inside its declared contexts. -/
def contextSpan (language : LanguageDef) (sites : List Site) : ReductionSpan Pattern where
  Edge := {pair : Pattern × Pattern // ContextStep language sites pair.1 pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

theorem object_argument {label : String} {before after : List Pattern} {argument : Pattern}
    (state : ObjectState (.apply label (before ++ argument :: after))) : ObjectState argument := by
  obtain ⟨inScope, object⟩ := state
  simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
  simp only [Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern] at object
  exact ⟨inScope argument (by simp), objects_of_list object argument (by simp)⟩

variable {A : Type} [DecidableEq A]

namespace Certificate

variable (certificate : Certificate A)

/-- **Every declared site respects the preorder**: lowering the argument at the site lowers the term. -/
def sitesCheck (sites : List Site) : Bool :=
  sites.all fun site =>
    (vectors certificate.elements site.2.1).all fun arguments =>
      certificate.elements.all fun lower =>
        !certificate.below (arguments.getD site.2.2 certificate.model.junk) lower ||
          certificate.below (certificate.model.operation site.1 arguments)
            (certificate.model.operation site.1 (arguments.set site.2.2 lower))

variable {certificate} {language : LanguageDef} {sites : List Site}

theorem site_below (checked : certificate.sitesCheck sites = true) {label : String} {before after : List A}
    {first second : A} (declared : (label, before.length + after.length + 1, before.length) ∈ sites)
    (low : certificate.below first second = true) :
    certificate.below (certificate.model.operation label (before ++ first :: after))
      (certificate.model.operation label (before ++ second :: after)) = true := by
  have siteChecked := List.all_eq_true.mp checked _ declared
  have arguments := List.all_eq_true.mp siteChecked (before ++ first :: after)
    ((mem_vectors certificate.elements certificate.complete _ _).mpr (by simp))
  have lowered := List.all_eq_true.mp arguments second (certificate.complete second)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some, low, Bool.not_true, Bool.false_or] at lowered
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.set_cons_zero] at lowered
  exact lowered

/-- **Every step inside a declared context from a scoped state goes down the preorder.** -/
theorem contextStep_below (valid : certificate.valid language = true) (sitesChecked : certificate.sitesCheck sites = true) :
    ∀ {source target : Pattern}, ContextStep language sites source target → ObjectState source →
      certificate.below (value certificate.model source) (value certificate.model target) = true
  | _, _, .root step, inScope => step_below valid inScope step
  | _, _, .inside (before := before) (after := after) declared inner, inScope => by
    have low := contextStep_below valid sitesChecked inner (object_argument inScope)
    unfold value at low ⊢
    simp only [eval, evalList_eq_map, List.map_append, List.map_cons]
    exact site_below sitesChecked (by simpa using declared) low

/-- **The steps inside declared contexts go down.** -/
theorem contextsGoDown (valid : certificate.valid language = true) (sitesChecked : certificate.sitesCheck sites = true) :
    certificate.GoesDown (contextSpan language sites) :=
  fun event inScope => contextStep_below valid sitesChecked event.2 inScope

/-- **Decide that a state cannot reach the goals, with steps inside the declared contexts.** -/
def cannotReachInContexts (language : LanguageDef) (sites : List Site) (goals : List Pattern) (accept : A → Bool)
    (state : Pattern) : Bool :=
  certificate.cannotReach language goals accept state && certificate.sitesCheck sites

theorem cannotReachInContexts_of_check {goals : List Pattern} {accept : A → Bool} {state : Pattern}
    (checked : certificate.cannotReachInContexts language sites goals accept state = true) :
    ¬ Reaches (between (contextSpan language sites) ObjectState) (Goal goals) state := by
  simp only [cannotReachInContexts, cannotReach, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨valid, goalsChecked⟩, apartChecked⟩, sitesChecked⟩ := checked
  exact certificate.not_reaches_of_apart (preorderValid_of_valid valid) (contextsGoDown valid sitesChecked)
    goalsChecked apartChecked

end Certificate

end Mettapedia.OSLF.Framework.FiniteModels
