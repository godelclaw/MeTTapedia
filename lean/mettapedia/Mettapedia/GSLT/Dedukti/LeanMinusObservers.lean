import Mettapedia.GSLT.Core.StepFree
import Mettapedia.GSLT.Dedukti.LeanMinusCanonicity
import Mettapedia.GSLT.Dedukti.LeanMinusPaperNormalForm
import Mettapedia.GSLT.Dedukti.LeanMinusFrozenAgreement
import Mettapedia.GSLT.Dedukti.TypePreservation
import Mettapedia.GSLT.Contexts.TermsAlone
import Mettapedia.GSLT.Distinction.Dictionary
import Mettapedia.Logic.HostingStyles.Observers
import Mettapedia.Logic.TheoryModel.EpsilonHosting

/-!
# The translations of Lean's universe levels into Dedukti, as observers of levels

A translation of Lean's universe levels into a theory of the λΠ-calculus modulo
observes the levels: two levels are indistinguishable for it when their codes
are convertible (`codeObserver`, the crisp observer of the report
`codeReport`, the class of the code in the conversion presentation).  The
levels have their own observer, the semantic one: two levels are
indistinguishable when they have one value at every valuation of the level
variables (`semanticObserver`, of the report `semanticReport`).  This module
places four translations of the Dedukti encoding of Lean (arXiv 2609.24604)
against the semantic observer in the refinement order `Tolerance.Extends`, in
which `fine.Extends coarse` says that `coarse` separates no more than `fine`.

## The table

| | Translation | Its observer | Against the semantic observer | Keeps | Loses | Adds |
|---|---|---|---|---|---|---|
| (a) | the paper's code `paperCode` into the paper's level theory `paperLevelTheory` | `paperObserver`, the normal-form report of the paper's own rules (`paperObserver_eq_normalForm`) | **incomparable** (`paper_incomparable_with_semantic`) | every distinction that shows at a valuation positive everywhere (`paper_strictly_finer_than_positive`) | `max 1 α` against `α` (`paperLostFiber`); nothing but distinctions that show only at valuations that give `0` to a variable of the two levels (`eval_eq_of_conv_paperCode_on_variables`) | `max (succ α) (max 2 α)` against `max 2 (succ α)` (`paperAddedFiber`) |
| (b) | the paper's code with universe polymorphism `paperLevel parameter` into the paper's theory `leanTheory` | `polyObserver parameter`, the observer that identifies everything (`polyObserver_eq_top`) | **strictly coarser** (`poly_strictly_coarser_than_semantic`) | nothing | every distinction (`polyLostFiber`) | nothing |
| (c) | the repaired code `code` into the theory with explicit level substitution `leanTheoryExplicit` | `explicitObserver`, the normal-form report `normalSet` (`explicitObserver_eq_normalForm`) | **equal**, for all levels with any number of variables (`explicitObserver_eq_semantic`) | every distinction | nothing | nothing |
| (d) | the frozen-parameter code `paperLevel frzVar` into the frozen strategy over the corrected rules `frozenTheoryCorrected` | `frozenObserver`, equal to (c) (`frozenObserver_eq_explicit`) | **equal**, for all levels (`frozenObserver_eq_semantic`) | every distinction | nothing | nothing |

The equality of (c) is the paper's Theorems 2 and 3 for the repaired code and
all levels (`theorem2_all_levels`): the normal-form report and the semantic
report are functions of each other (`semanticReport_factors_normalSet`,
`normalSet_factors_semanticReport`).  It holds inside a declaration as well,
where (b) collapses: read in the frame variable of the declaration, the
repaired code induces the semantic observer
(`explicitObserver_in_declaration_eq_semantic`).

Three controls beside the table.

* **Trying the two rules on `v` in order does not repair (b)**: with the
  paper's rules tried in order, every translation still induces the observer
  that identifies everything (`orderedCodeObserver_lean_eq_top`).  When no two
  rules overlap, trying them in order is invisible to the observer of every
  translation (`orderedCodeObserver_eq_of_orthogonal`).
* **Freezing the parameters does not repair the level theory**: on the paper's
  own rules the frozen-parameter code is incomparable with the semantic
  observer, as (a) is (`frozenPaper_incomparable_with_semantic`).
* **The two defects of (a), one at a time.**

  | | the rule on `Add` corrected | the paper's rule on `Add` |
  |---|---|---|
  | each variable in its own guard | (c): **equal** | `guardedObserver`: **strictly finer** (`guarded_strictly_finer_than_semantic`) |
  | the empty guard | `unguardedObserver`: **strictly coarser** (`unguarded_strictly_coarser_than_semantic`) | (a): **incomparable** |

  The empty guard alone is exactly the observer that evaluates levels at the
  positive valuations (`unguardedObserver_eq_positive`): it loses, and adds
  nothing.  The paper's rule on `Add` alone adds, and loses nothing.  (a) is
  strictly finer than the empty guard alone
  (`paper_strictly_finer_than_unguarded`), and incomparable with the guard
  corrected alone, already on equivalent levels
  (`paper_incomparable_with_guarded`): the pairs that the rule on `Add` fails
  to join depend on the guards.

With `∧` given by three overlapping rules, as the paper's figure writes it
(`pureTheory`), the lost distinction of (a) is the same
(`transcribed_not_extends_semantic`); the added one is proved for the
orthogonal `∧` only.

## How much is lost

The pair that (a) identifies wrongly differs at the valuations that give `α`
the value `0`, and at no other (`maxOneVar_eval_eq_iff`).

* An observer that evaluates levels at a set of valuations
  (`valuationObserver`) separates the pair exactly when one of its valuations
  gives `α` the value `0` (`valuation_indistinguishable_max_one_var_iff`); the
  observer of the positive valuations does not
  (`positive_indistinguishable_max_one_var`).
* **All of what (a) loses is of this kind**: two levels whose codes the
  paper's level theory converts have one value at every valuation that is
  positive on the variables of the two levels
  (`eval_eq_of_conv_paperCode_on_variables`).  The report at the valuations
  that are positive everywhere is a function of the normal form of the paper's
  rules (`positiveReport_factors_paperSet`), so (a) refines the observer of
  the positive valuations, strictly (`paper_strictly_finer_than_positive`).
  The cause is the empty guard of the code of a variable, which makes the
  dominance test unsound exactly where the variable is `0`; the paper's rule on
  `Add` loses no value (`addSubPaper_sound`).
* **The empty guard loses exactly this**: with the rule on `Add` corrected, the
  paper's code decides the equivalence of levels over the positive valuations,
  no more and no less (`unguardedObserver_eq_positive`,
  `unguarded_validated_iff_positive`).
* **Graded, by tests**: for every finitely supported weighting of value tests,
  the distance between `max 1 α` and `α` in the weighted tolerance of the tests
  is the mass of the tests at `α = 0` that ask for the value `0` or `1`
  (`withinTest_max_one_var_iff`, `testTolerance_distance_max_one_var`).  Any
  two levels that (a) identifies are no further apart than the mass of the
  tests that give the value `0` to one of their variables (`paper_withinTest`,
  `paper_testTolerance_distance_le`), and a weighted observer that tests only
  at valuations positive on their variables does not separate them
  (`paper_testTolerance_indistinguishable`).
* **Graded, by hosting** (`positive_hosting_weight_le`,
  `positive_hosting_single_iff`): with valuations as structures and level
  equations as sentences, every equation that (a) validates is a consequence
  of the positive valuations (`paper_validated_by_positive`), and the positive
  valuations host the level semantics up to `ε` only if `ε` is at least the
  weight of each tested equation such as `max 1 α = α`.  The notion
  `EpsHosts` grades a universe of structures; it grades (a) through the
  positive valuations, not as a translation.

## Preservation grades

From the semantic observer of levels to the checker's observer of terms
(`termObserver`, of which the observer of a translation is the pullback,
`codeObserver_eq_pullback`), a translation has a one-sided defect, the most
distance it adds, and a two-sided defect, the most distance it changes
(`Tolerance.ExpandsAtMost`, `Tolerance.DistortsAtMost`).  The observers are
crisp, so a defect is `0` or `1`.

| | adds at most | changes at most | |
|---|---|---|---|
| (a) | `1` | `1` | `paper_grades` |
| (b) | `0` | `1` | `poly_grades` |
| (c) | `0` | `0` | `explicit_distortsAtMost_zero` |
| (d) | `0` | `0` | `frozen_distortsAtMost_zero` |
| the empty guard alone | `0` | `1` | `unguarded_grades` |
| the guard corrected alone | `1` | `1` | `guarded_grades` |

## As maps of theories

The levels of a collection, compared by their equivalence and with no
reduction, are a theory given by its terms (`levelsWhere`).  A translation
that respects the equivalence is a map into the conversion presentation of its
target (`translationMap`); it is hosting exactly when it reflects the
equivalence (`translationMap_hosting_iff`).  In the vocabulary of observers:
being a map is the semantic observer refining the observer of the code
(`respects_iff_semantic_extends`), and hosting is the converse refinement
(`translationMap_hosting_iff_extends`).

* (c) is a hosting map on every collection of levels
  (`explicitCodeMap_hosting`), and it is not exhausting
  (`explicitCodeMap_not_exhausting`).  (d) likewise (`frozenCodeMap_hosting`,
  `frozenCodeMap_not_exhausting`).
* (a) is not a map of the theory of all levels (`paperCode_not_a_map`), and on
  every collection that holds `max 1 α` and `α` a map whose map on terms is the
  paper's code is not hosting (`paperCode_not_hosting`).
* (b): every translation is a map into the paper's theory (`polyMap`), and no
  map into it is hosting from a collection with two levels apart
  (`poly_not_hosting`, by `not_hosting_into_total_of_apart`,
  `polyMap_hosting_iff`).

## Rule order, and typing

The reading of the order of the two rules on `v` as two events is in
`LeanMinusRuleOrder` (`paper_select_instantiate_not_commute`,
`paper_fallback_not_independent`, `orthogonalConcurrency`).  For the observers
of levels the order is invisible when no two rules overlap, and it does not
repair (b) (`orderedCodeObserver_eq_of_orthogonal`,
`orderedCodeObserver_lean_eq_top`).

Typing is an observer of terms (`typingReport`).  A step out of a typed term is
invisible to it exactly when the target has the type
(`typing_indistinguishable_iff`), and type preservation at a type is the
hosting of its inhabitants, as they run, by the calculus as it runs
(`forgetTyping_hosting_iff`).  For the transcribed rule on `PUnit.rec` of the
theory with explicit level substitution both fail
(`punitRec_step_apart_for_typing`, `punitRec_forgetTyping_not_hosting`).  For
the Dedukti checker on the paper's own theory, where the two rules on `v` are
tried in order, there is a pair of the same kind with a beta step:
`sigma_only_forged.dk` is accepted and its beta-reduct `sigma_only_reduct.dk`
is rejected, in `artifacts/dedukti-sigma-poly-negative-20261008/` of the Lean
package.  That pair is evidence of a checker, not a theorem of this module.

The positive and negative examples of the definitions are in
`LeanMinusObserversControls`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Logic.HostingStyles (observer observer_indistinguishable)
open Mettapedia.GSLT.Distinction.Dictionary (ofReport_extends_iff_soundKey)

universe u

/-! ## A total target hosts nothing with two terms apart -/

/-- **A theory whose terms are all identified hosts no theory in which two
terms are kept apart.**  `Mettapedia.Logic.HostingStyles.not_hosting_into_total`
states this for a source that is the theory of a proof system with its
derivations kept apart; here the source is any theory presented through its
contexts. -/
theorem not_hosting_into_total_of_apart {source target : ContextTheory.{u}}
    (identified : ∀ (interface : target.Interface) (first second : target.Term interface),
      (target.equations interface).r first second)
    (map : ContextMap source target) {origin : source.Interface} {first second : source.Term origin}
    (distinct : ¬ (source.equations origin).r first second) : ¬ map.Hosting :=
  ContextMap.not_hosting_of_identifies map distinct (identified _ _ _)

/-! ## Crisp observers with one kernel -/

/-- Tolerances with one similarity are one tolerance. -/
theorem tolerance_eq_of_similarity {V : Type} {first second : Tolerance V}
    (same : first.similarity = second.similarity) : first = second := by
  cases first
  cases second
  dsimp only at same
  subst same
  rfl

/-- **Reports with one kernel have one crisp observer.** -/
theorem observer_eq_of_kernel {V W W' : Type} {first : V → W} {second : V → W'}
    (same : ∀ left right : V, first left = first right ↔ second left = second right) :
    observer first = observer second := by
  classical
  apply tolerance_eq_of_similarity
  funext left right
  change (if first left = first right then (1 : ℚ) else 0) =
    if second left = second right then 1 else 0
  exact if_congr (same left right) rfl rfl

/-- **Coarsening of crisp observers is constancy on fibres**: the crisp
observer of `fine` extends to that of `coarse` exactly when `coarse` is
constant on the fibres of `fine`.  This is
`Dictionary.ofReport_extends_iff_soundKey` for the observer of a report whose
equality is decided classically. -/
theorem observer_extends_iff {V W W' : Type} (fine : V → W) (coarse : V → W') :
    (observer fine).Extends (observer coarse) ↔ ConstantOnFibers fine coarse :=
  @ofReport_extends_iff_soundKey V W W' (fun _ _ => Classical.propDecidable _)
    (fun _ _ => Classical.propDecidable _) fine coarse

/-- **A lost distinction refutes the refinement**: a non-trivial fibre of
`fine` against `coarse` shows that the crisp observer of `fine` does not extend
to that of `coarse`. -/
theorem not_observer_extends_of_fiber {V W W' : Type} {fine : V → W} {coarse : V → W'}
    (fiber : NonTrivialFiber fine coarse) : ¬ (observer fine).Extends (observer coarse) :=
  fun coarser => fiber.not_constantOnFibers ((observer_extends_iff fine coarse).mp coarser)

/-- Restricting the crisp observer of a report is observing the restricted
report. -/
theorem pullback_observer {U V W : Type} (report : V → W) (restrict : U → V) :
    (observer report).pullback restrict = observer (report ∘ restrict) :=
  rfl

/-- The distance of a crisp observer is `0` on points with one report and `1`
on the others. -/
theorem observer_distance_cases {V W : Type} (report : V → W) (first second : V) :
    ((observer report).distance first second = 0 ∧ report first = report second) ∨
      ((observer report).distance first second = 1 ∧ report first ≠ report second) := by
  classical
  by_cases same : report first = report second
  · exact Or.inl ⟨(observer_indistinguishable report first second).mpr same, same⟩
  · refine Or.inr ⟨?_, same⟩
    change (1 : ℚ) - (if report first = report second then 1 else 0) = 1
    rw [if_neg same, sub_zero]

/-- **A map between crisp observers adds no distance exactly when it carries
points with one report to points with one report.** -/
theorem observer_expandsAtMost_zero_iff {V W X Y : Type} (source : V → X) (target : W → Y)
    (map : V → W) :
    Tolerance.ExpandsAtMost (observer source) (observer target) map 0 ↔
      ∀ first second : V, source first = source second → target (map first) = target (map second) := by
  constructor
  · intro expands first second same
    have bound := expands first second
    rw [(observer_indistinguishable source first second).mpr same, add_zero] at bound
    rcases observer_distance_cases target (map first) (map second) with ⟨_, equal⟩ | ⟨one, _⟩
    · exact equal
    · rw [one] at bound
      norm_num at bound
  · intro carries first second
    rcases observer_distance_cases source first second with ⟨zero, same⟩ | ⟨one, _⟩
    · rw [zero, (observer_indistinguishable target _ _).mpr (carries first second same)]
      norm_num
    · rw [one]
      have bounded := Tolerance.distance_bounded (observer target) (map first) (map second)
      linarith

/-- **A map between crisp observers that separates two points with one report
has one-sided defect `1`**: it has no one-sided grade above `0`. -/
theorem not_expandsAtMost_of_separated {V W X Y : Type} {source : V → X} {target : W → Y}
    {map : V → W} {first second : V} (same : source first = source second)
    (apart : target (map first) ≠ target (map second)) {δ : ℚ} (small : δ < 1) :
    ¬ Tolerance.ExpandsAtMost (observer source) (observer target) map δ := by
  intro expands
  have bound := expands first second
  rw [(observer_indistinguishable source first second).mpr same] at bound
  rcases observer_distance_cases target (map first) (map second) with ⟨_, equal⟩ | ⟨one, _⟩
  · exact apart equal
  · rw [one] at bound
    linarith

/-- **A map between crisp observers changes no distance exactly when it keeps
and reflects equality of reports.** -/
theorem observer_distortsAtMost_zero_iff {V W X Y : Type} (source : V → X) (target : W → Y)
    (map : V → W) :
    Tolerance.DistortsAtMost (observer source) (observer target) map 0 ↔
      ∀ first second : V, source first = source second ↔ target (map first) = target (map second) := by
  constructor
  · intro distorts first second
    have bound := distorts first second
    rcases observer_distance_cases source first second with ⟨sourceZero, same⟩ | ⟨sourceOne, apart⟩ <;>
      rcases observer_distance_cases target (map first) (map second) with
        ⟨targetZero, equal⟩ | ⟨targetOne, distinct⟩
    · exact ⟨fun _ => equal, fun _ => same⟩
    · rw [sourceZero, targetOne] at bound
      norm_num at bound
    · rw [sourceOne, targetZero] at bound
      norm_num at bound
    · exact ⟨fun same => absurd same apart, fun equal => absurd equal distinct⟩
  · intro agrees first second
    rcases observer_distance_cases source first second with ⟨sourceZero, same⟩ | ⟨sourceOne, apart⟩
    · rw [sourceZero, (observer_indistinguishable target _ _).mpr ((agrees first second).mp same)]
      norm_num
    · rcases observer_distance_cases target (map first) (map second) with
        ⟨_, equal⟩ | ⟨targetOne, _⟩
      · exact absurd ((agrees first second).mpr equal) apart
      · rw [sourceOne, targetOne]
        norm_num

/-- **A map between crisp observers that identifies two points with different
reports has two-sided defect `1`.** -/
theorem not_distortsAtMost_of_identified {V W X Y : Type} {source : V → X} {target : W → Y}
    {map : V → W} {first second : V} (apart : source first ≠ source second)
    (same : target (map first) = target (map second)) {δ : ℚ} (small : δ < 1) :
    ¬ Tolerance.DistortsAtMost (observer source) (observer target) map δ := by
  intro distorts
  have bound := distorts first second
  rw [(observer_indistinguishable target _ _).mpr same] at bound
  rcases observer_distance_cases source first second with ⟨_, equal⟩ | ⟨one, _⟩
  · exact apart equal
  · rw [one] at bound
    norm_num at bound
    linarith

/-! ## What the checker of a theory can tell -/

/-- **What the checker of a theory can tell about a term**: its class in the
conversion presentation of the theory. -/
def conversionClass (theory : Theory) (term : Term) :
    Quotient ((conversionTheory theory).equations ()) :=
  Quotient.mk _ term

theorem conversionClass_eq_iff {theory : Theory} {first second : Term} :
    conversionClass theory first = conversionClass theory second ↔ Conv theory first second :=
  ⟨fun same => conversionTheory_equations.mp (Quotient.exact same),
    fun convertible => Quotient.sound (conversionTheory_equations.mpr convertible)⟩

/-- **The checker's observer of the terms of a theory**: two terms are
indistinguishable when they are convertible. -/
noncomputable abbrev termObserver (theory : Theory) : Tolerance Term :=
  observer (conversionClass theory)

/-! ## Typing as an observer, and type preservation as hosting -/

/-- **What the typing observer of a context and a type reports about a term**:
whether the term has the type in the context. -/
def typingReport (theory : Theory) (context : Ctx) (type term : Term) : Prop :=
  LambdaPiModulo theory context term type

/-- **A step out of a typed term is invisible to the typing observer exactly
when its target has the type.** -/
theorem typing_indistinguishable_iff {theory : Theory} {context : Ctx} {type source target : Term}
    (typed : LambdaPiModulo theory context source type) :
    (observer (typingReport theory context type)).Indistinguishable source target ↔
      LambdaPiModulo theory context target type := by
  rw [observer_indistinguishable]
  constructor
  · intro same
    have transported : typingReport theory context type target := same ▸ typed
    exact transported
  · intro targetTyped
    exact propext ⟨fun _ => targetTyped, fun _ => typed⟩

/-- **The inhabitants of one type in one context, as they run**: compared by
identity, and reduced by the steps of the theory between inhabitants. -/
def typedRewriting (theory : Theory) (context : Ctx) (type : Term) : GSLT.{0} where
  Term := {term : Term // LambdaPiModulo theory context term type}
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first second => Step theory first.1 second.1
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **Forgetting the type of the inhabitants as they run**: into the calculus
as it runs. -/
def forgetTyping (theory : Theory) (context : Ctx) (type : Term) :
    ContextMap (typedRewriting theory context type).termsAlone (rewritingTheory theory) :=
  ContextMap.ofTerms () (fun term => term.1) (fun same => congrArg Subtype.val same)

/-- **Type preservation at a type is hosting of its inhabitants by the
calculus**: forgetting the type is a hosting map exactly when every step out
of an inhabitant leads to an inhabitant.  The law at stake is the reflection
of transitions: a step of the image must come from the source. -/
theorem forgetTyping_hosting_iff (theory : Theory) (context : Ctx) (type : Term) :
    (forgetTyping theory context type).Hosting ↔
      ∀ source target : Term, LambdaPiModulo theory context source type → Step theory source target →
        LambdaPiModulo theory context target type := by
  refine (ContextMap.ofTerms_hosting_iff (source := typedRewriting theory context type)
    (target := rewritingTheory theory) () (fun term => term.1)
    (fun same => congrArg Subtype.val same)).trans ⟨?_, ?_⟩
  · rintro ⟨_, _, reflects⟩ source target typed step
    obtain ⟨sourceNext, _, same⟩ := reflects ⟨source, typed⟩ target step
    have equal : target = sourceNext.1 := same
    rw [equal]
    exact sourceNext.2
  · intro preserves
    exact ⟨fun first second same => Subtype.ext same, fun _ _ step => step,
      fun first next step => ⟨⟨next, preserves first.1 next first.2 step⟩, step, rfl⟩⟩

end Mettapedia.GSLT.Dedukti

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Ctx Sig)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Logic.HostingStyles (observer observer_indistinguishable observer_apart
  observer_extends_of_factors)
open Mettapedia.Logic.TheoryModel (SentenceWeighting WithinTest EpsHosts weight_le_of_leak models
  modelsIn consequencesIn epsHosts_iff testTolerance testTolerance_distance
  testTolerance_indistinguishable_iff withinTest_iff_testDistance_le)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## The semantic observer -/

/-- **What the semantics reports about a level**: its value at every valuation
of the level variables. -/
def semanticReport (level : LeanLevel) : (Nat → Nat) → Nat := fun valuation => level.eval valuation

theorem semanticReport_eq_iff {first second : LeanLevel} :
    semanticReport first = semanticReport second ↔ LeanLevel.Equiv first second :=
  ⟨fun same valuation => congrFun same valuation, fun equivalent => funext equivalent⟩

/-- **The semantic observer of levels**: two levels are indistinguishable when
they are equivalent. -/
noncomputable abbrev semanticObserver : Tolerance LeanLevel := observer semanticReport

theorem semanticObserver_indistinguishable {first second : LeanLevel} :
    semanticObserver.Indistinguishable first second ↔ LeanLevel.Equiv first second :=
  (observer_indistinguishable _ _ _).trans semanticReport_eq_iff

/-! ## The observer of a translation -/

/-- **What a translation of levels reports about a level**: the class of its
code in the conversion presentation of the target. -/
def codeReport (theory : Theory) (translate : LeanLevel → Term) (level : LeanLevel) :
    Quotient ((conversionTheory theory).equations ()) :=
  conversionClass theory (translate level)

theorem codeReport_eq_iff {theory : Theory} {translate : LeanLevel → Term} {first second : LeanLevel} :
    codeReport theory translate first = codeReport theory translate second ↔
      Conv theory (translate first) (translate second) :=
  conversionClass_eq_iff

/-- **The observer that a translation induces on levels**: two levels are
indistinguishable when their codes are convertible in the target. -/
noncomputable abbrev codeObserver (theory : Theory) (translate : LeanLevel → Term) :
    Tolerance LeanLevel :=
  observer (codeReport theory translate)

theorem codeObserver_indistinguishable {theory : Theory} {translate : LeanLevel → Term}
    {first second : LeanLevel} :
    (codeObserver theory translate).Indistinguishable first second ↔
      Conv theory (translate first) (translate second) :=
  (observer_indistinguishable _ _ _).trans codeReport_eq_iff

/-! ## The observers of evaluation at some valuations -/

/-- What an observer reports that evaluates a level at the valuations of a set
only. -/
def valuationReport (tests : Set (Nat → Nat)) (level : LeanLevel) : tests → Nat :=
  fun valuation => level.eval valuation.1

theorem valuationReport_eq_iff {tests : Set (Nat → Nat)} {first second : LeanLevel} :
    valuationReport tests first = valuationReport tests second ↔
      ∀ valuation ∈ tests, first.eval valuation = second.eval valuation :=
  ⟨fun same valuation member => congrFun same ⟨valuation, member⟩,
    fun agree => funext fun valuation => agree valuation.1 valuation.2⟩

/-- The observer that evaluates levels at the valuations of a set only. -/
noncomputable abbrev valuationObserver (tests : Set (Nat → Nat)) : Tolerance LeanLevel :=
  observer (valuationReport tests)

theorem valuationObserver_indistinguishable {tests : Set (Nat → Nat)} {first second : LeanLevel} :
    (valuationObserver tests).Indistinguishable first second ↔
      ∀ valuation ∈ tests, first.eval valuation = second.eval valuation :=
  (observer_indistinguishable _ _ _).trans valuationReport_eq_iff

/-- The valuations that give every level variable a positive value. -/
def positiveValuations : Set (Nat → Nat) := {valuation | ∀ index, valuation index ≠ 0}

/-- The report at the valuations of a set is a function of the semantic report:
restrict it. -/
theorem valuationReport_factors_semantic (tests : Set (Nat → Nat)) :
    Factors semanticReport (valuationReport tests) :=
  ⟨fun value valuation => value valuation.1, fun _ => rfl⟩

/-- **The semantic observer refines every observer that evaluates at some
valuations.** -/
theorem semantic_extends_valuation (tests : Set (Nat → Nat)) :
    semanticObserver.Extends (valuationObserver tests) :=
  observer_extends_of_factors (valuationReport_factors_semantic tests)

/-- Evaluating at more valuations refines. -/
theorem valuationObserver_anti {fewer more : Set (Nat → Nat)} (included : fewer ⊆ more) :
    (valuationObserver more).Extends (valuationObserver fewer) :=
  observer_extends_of_factors
    ⟨fun value valuation => value ⟨valuation.1, included valuation.2⟩, fun _ => rfl⟩

/-- Evaluating at every valuation is the semantic observer. -/
theorem valuationObserver_univ : valuationObserver Set.univ = semanticObserver :=
  observer_eq_of_kernel fun _ _ =>
    valuationReport_eq_iff.trans
      ⟨fun agree => semanticReport_eq_iff.mpr fun valuation => agree valuation trivial,
        fun same valuation _ => semanticReport_eq_iff.mp same valuation⟩

/-! ## (a) The paper's code into the paper's level theory: incomparable -/

/-- **(a)** The observer of the paper's code (Definition 2) into the paper's
level theory `ΣU`, `ΣP`. -/
noncomputable abbrev paperObserver : Tolerance LeanLevel := codeObserver paperLevelTheory paperCode

/-- `max 1 α` reduces to `α` in the paper's level theory with `∧` given by its
four rules on literals, the theory in which the codes of two equivalent levels
are kept apart (`paper_add_incomplete`). -/
theorem paperLevelTheory_max_one_var_reduces :
    Reduces paperLevelTheory (paperCode maxOneVar) (paperCode alpha) :=
  Reduces.of_evaluate paperLevelRules_linear (fuel := 200) (by decide +kernel)

/-- **The distinction that (a) loses**: `max 1 α` and `α` have one code up to
conversion, and different values at `α = 0`. -/
def paperLostFiber : NonTrivialFiber (codeReport paperLevelTheory paperCode) semanticReport where
  left := maxOneVar
  right := alpha
  sameShadow := codeReport_eq_iff.mpr paperLevelTheory_max_one_var_reduces.conv
  differentValue := fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same)

/-- **The distinction that (a) adds**: `max (succ α) (max 2 α)` and
`max 2 (succ α)` have one value at every valuation, and codes that are not
convertible. -/
def paperAddedFiber : NonTrivialFiber semanticReport (codeReport paperLevelTheory paperCode) where
  left := addPairLeft
  right := addPairRight
  sameShadow := semanticReport_eq_iff.mpr paper_add_incomplete.1
  differentValue := fun same => paper_add_incomplete.2 (codeReport_eq_iff.mp same)

/-- **(a) is incomparable with the semantic observer**: it does not refine it
(`paperLostFiber`) and is not refined by it (`paperAddedFiber`). -/
theorem paper_incomparable_with_semantic :
    ¬ paperObserver.Extends semanticObserver ∧ ¬ semanticObserver.Extends paperObserver :=
  ⟨not_observer_extends_of_fiber paperLostFiber, not_observer_extends_of_fiber paperAddedFiber⟩

/-- **(a) is the crisp observer of the normal-form report of the paper's own
rules**: the set computed with the paper's rule on `Add` and the empty guard,
for all levels. -/
theorem paperObserver_eq_normalForm :
    paperObserver = observer (normalSetWith addSubPaper unguardedLeaf) :=
  observer_eq_of_kernel fun _ _ => codeReport_eq_iff.trans conv_paperCode_iff

/-- The same lost distinction with `∧` as the paper's figure writes it (three
overlapping rules): the transcription `pureTheory`. -/
def transcribedLostFiber : NonTrivialFiber (codeReport pureTheory paperCode) semanticReport where
  left := maxOneVar
  right := alpha
  sameShadow := codeReport_eq_iff.mpr paper_max_one_var_reduces.conv
  differentValue := fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same)

/-- With `∧` as the figure writes it, the paper's code does not refine the
semantic observer either. -/
theorem transcribed_not_extends_semantic :
    ¬ (codeObserver pureTheory paperCode).Extends semanticObserver :=
  not_observer_extends_of_fiber transcribedLostFiber

/-! ## (b) The paper's code with universe polymorphism: the total observer -/

/-- **(b)** The observer of the paper's code with universe polymorphism:
Definition 3 into the paper's theory, the level variables of the declaration
being the terms `parameter i`. -/
noncomputable abbrev polyObserver (parameter : Nat → Term) : Tolerance LeanLevel :=
  codeObserver leanTheory (paperLevel parameter)

/-- **Every translation of levels into the paper's theory induces the observer
that identifies everything.** -/
theorem codeObserver_leanTheory_eq_top (translate : LeanLevel → Term) :
    codeObserver leanTheory translate = Tolerance.top := by
  apply tolerance_eq_of_similarity
  funext first second
  exact (Tolerance.indistinguishable_iff_similarity_one _ _ _).mp
    (codeObserver_indistinguishable.mpr (leanTheory_conv_all _ _))

/-- **(b) is the total observer.** -/
theorem polyObserver_eq_top (parameter : Nat → Term) : polyObserver parameter = Tolerance.top :=
  codeObserver_leanTheory_eq_top _

/-- A distinction of the semantics that every translation into the paper's
theory loses: the levels `0` and `1`. -/
def polyLostFiber (translate : LeanLevel → Term) :
    NonTrivialFiber (codeReport leanTheory translate) semanticReport where
  left := .zero
  right := .succ .zero
  sameShadow := codeReport_eq_iff.mpr (leanTheory_conv_all _ _)
  differentValue := fun same => by
    have atZero := semanticReport_eq_iff.mp same fun _ => 0
    simp [LeanLevel.eval] at atZero

/-- **(b) is strictly coarser than the semantic observer**, and it loses every
distinction: any two levels are indistinguishable for it. -/
theorem poly_strictly_coarser_than_semantic (parameter : Nat → Term) :
    semanticObserver.Extends (polyObserver parameter) ∧
      ¬ (polyObserver parameter).Extends semanticObserver ∧
      ∀ first second : LeanLevel, (polyObserver parameter).Indistinguishable first second := by
  refine ⟨?_, ?_, fun first second => codeObserver_indistinguishable.mpr (leanTheory_conv_all _ _)⟩
  · rw [polyObserver_eq_top]
    exact Tolerance.extends_top _
  · exact not_observer_extends_of_fiber (polyLostFiber _)

/-! ### The rules tried in order -/

/-- **What a checker that tries the rules in order can tell about a term**:
its class for the equivalence that the ordered steps generate. -/
def orderedClass (signature : Sig) (rules : List RewriteRule) (term : Term) :
    Quotient (⟨OrderedConv signature rules, Relation.EqvGen.is_equivalence _⟩ : Setoid Term) :=
  Quotient.mk _ term

theorem orderedClass_eq_iff {signature : Sig} {rules : List RewriteRule} {first second : Term} :
    orderedClass signature rules first = orderedClass signature rules second ↔
      OrderedConv signature rules first second :=
  ⟨fun same => Quotient.exact same, fun convertible => Quotient.sound convertible⟩

/-- **The observer that a translation induces when the checker tries the rules
in order.** -/
noncomputable abbrev orderedCodeObserver (signature : Sig) (rules : List RewriteRule)
    (translate : LeanLevel → Term) : Tolerance LeanLevel :=
  observer fun level => orderedClass signature rules (translate level)

/-- **Trying the two rules on `v` in order does not repair (b)**: for the
paper's rules tried in order, every translation of levels still induces the
observer that identifies everything. -/
theorem orderedCodeObserver_lean_eq_top (translate : LeanLevel → Term) :
    orderedCodeObserver leanSig leanRules translate = Tolerance.top := by
  apply tolerance_eq_of_similarity
  funext first second
  exact (Tolerance.indistinguishable_iff_similarity_one _ _ _).mp
    ((observer_indistinguishable _ _ _).mpr (orderedClass_eq_iff.mpr (ordered_conv_collapses _ _)))

/-- **When no two rules overlap, trying them in order is invisible**: the
observer that a translation induces is the one of the theory of the rules. -/
theorem orderedCodeObserver_eq_of_orthogonal {signature : Sig} {rules : List RewriteRule}
    (orthogonal : (Theory.ofSig signature rules).Orthogonal) (translate : LeanLevel → Term) :
    orderedCodeObserver signature rules translate =
      codeObserver (Theory.ofSig signature rules) translate := by
  have same : OrderedStep signature rules = Step (Theory.ofSig signature rules) :=
    funext fun _ => funext fun _ => propext (orderedStep_iff_of_orthogonal orthogonal)
  refine observer_eq_of_kernel fun first second =>
    orderedClass_eq_iff.trans (Iff.trans ?_ codeReport_eq_iff.symm)
  show Relation.EqvGen (OrderedStep signature rules) _ _ ↔
    Relation.EqvGen (Step (Theory.ofSig signature rules)) _ _
  rw [same]

/-! ## (c) The repaired code: the normal-form report -/

/-- **(c)** The observer of the repaired code into the theory with explicit
level substitution. -/
noncomputable abbrev explicitObserver : Tolerance LeanLevel := codeObserver leanTheoryExplicit code

/-- **(c) is the crisp observer of the normal-form report** `normalSet`, for
all levels. -/
theorem explicitObserver_eq_normalForm : explicitObserver = observer normalSet :=
  observer_eq_of_kernel fun _ _ => codeReport_eq_iff.trans conv_code_iff_normalSet

/-- **The semantic report is a function of the normal-form report**: the value
of a level at a valuation is the value of its computed set, for all levels. -/
theorem semanticReport_factors_normalSet : Factors normalSet semanticReport :=
  ⟨fun set valuation => setEval valuation set, fun level =>
    funext fun valuation => setEval_normalSet valuation level⟩

/-- **The normal-form report is a function of the semantic report**: levels with
one value at every valuation have one computed set, for all levels. -/
theorem normalSet_factors_semanticReport : Factors semanticReport normalSet := by
  classical
  refine ⟨fun value => if realized : ∃ level, semanticReport level = value
    then normalSet (Classical.choose realized) else [], fun level => ?_⟩
  have realized : ∃ other, semanticReport other = semanticReport level := ⟨level, rfl⟩
  change (if realized : ∃ other, semanticReport other = semanticReport level
    then normalSet (Classical.choose realized) else []) = normalSet level
  rw [dif_pos realized]
  exact normalSet_eq_of_equiv (semanticReport_eq_iff.mp (Classical.choose_spec realized))

/-- **(c) equals the semantic observer**, for all levels, with any number of
level variables: the repaired code loses no distinction and adds none. -/
theorem explicitObserver_eq_semantic : explicitObserver = semanticObserver :=
  observer_eq_of_kernel fun _ _ =>
    codeReport_eq_iff.trans (theorem2_all_levels.trans semanticReport_eq_iff.symm)

/-- **(c) inside a declaration**: read in the frame variable of a declaration,
as `sub x |l|`, the repaired code induces the semantic observer too.  This is
the counterpart, for the repaired theory, of the collapse (b). -/
theorem explicitObserver_in_declaration_eq_semantic (index : Nat) :
    codeObserver leanTheoryExplicit (levelIn (.var index)) = semanticObserver :=
  observer_eq_of_kernel fun _ _ =>
    codeReport_eq_iff.trans (theorem2_all_levels_in.trans semanticReport_eq_iff.symm)

/-! ## (d) The frozen-parameter code on the corrected rules: equal to (c) -/

/-- **(d)** The observer of the paper's code with frozen level parameters,
into the frozen strategy over the corrected rules. -/
noncomputable abbrev frozenObserver : Tolerance LeanLevel :=
  codeObserver frozenTheoryCorrected (paperLevel frzVar)

/-- **(d) equals (c)**, for all levels. -/
theorem frozenObserver_eq_explicit : frozenObserver = explicitObserver :=
  observer_eq_of_kernel fun _ _ =>
    codeReport_eq_iff.trans (frozenCorrected_agrees_with_explicit.trans codeReport_eq_iff.symm)

/-- **Theorems 2 and 3 for the frozen strategy over the corrected rules, for
all levels**: the frozen translations of two levels are convertible exactly
when the levels are equivalent. -/
theorem frozenCorrected_theorem2_all_levels {first second : LeanLevel} :
    Conv frozenTheoryCorrected (paperLevel frzVar first) (paperLevel frzVar second) ↔
      LeanLevel.Equiv first second :=
  frozenCorrected_agrees_with_explicit.trans theorem2_all_levels

/-- **(d) equals the semantic observer**, for all levels. -/
theorem frozenObserver_eq_semantic : frozenObserver = semanticObserver :=
  frozenObserver_eq_explicit.trans explicitObserver_eq_semantic

/-- The distinction that the frozen-parameter code loses on the paper's own
rules. -/
def frozenPaperLostFiber :
    NonTrivialFiber (codeReport frozenTheory (paperLevel frzVar)) semanticReport where
  left := maxOneVar
  right := alpha
  sameShadow := codeReport_eq_iff.mpr frozen_relates_max_one_var
  differentValue := fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same)

/-- The distinction that the frozen-parameter code adds on the paper's own
rules. -/
def frozenPaperAddedFiber :
    NonTrivialFiber semanticReport (codeReport frozenTheory (paperLevel frzVar)) where
  left := addPairLeft
  right := addPairRight
  sameShadow := semanticReport_eq_iff.mpr frozen_add_incomplete.1
  differentValue := fun same => frozen_add_incomplete.2 (codeReport_eq_iff.mp same)

/-- **Freezing the parameters does not repair the level theory**: on the
paper's own rules the frozen-parameter code is incomparable with the semantic
observer, as (a) is. -/
theorem frozenPaper_incomparable_with_semantic :
    ¬ (codeObserver frozenTheory (paperLevel frzVar)).Extends semanticObserver ∧
      ¬ semanticObserver.Extends (codeObserver frozenTheory (paperLevel frzVar)) :=
  ⟨not_observer_extends_of_fiber frozenPaperLostFiber,
    not_observer_extends_of_fiber frozenPaperAddedFiber⟩

/-! ## How much the empty guard loses -/

/-- `max 1 α` and `α` have one value exactly at the valuations at which `α` is
positive. -/
theorem maxOneVar_eval_eq_iff (valuation : Nat → Nat) :
    maxOneVar.eval valuation = alpha.eval valuation ↔ valuation 0 ≠ 0 := by
  simp only [maxOneVar, alpha, LeanLevel.eval, eval_natLevel]
  omega

/-- **An observer that evaluates at some valuations separates `max 1 α` from
`α` exactly when one of its valuations gives `α` the value `0`.** -/
theorem valuation_indistinguishable_max_one_var_iff (tests : Set (Nat → Nat)) :
    (valuationObserver tests).Indistinguishable maxOneVar alpha ↔
      ∀ valuation ∈ tests, valuation 0 ≠ 0 :=
  valuationObserver_indistinguishable.trans
    ⟨fun agree valuation member => (maxOneVar_eval_eq_iff valuation).mp (agree valuation member),
      fun positive valuation member => (maxOneVar_eval_eq_iff valuation).mpr (positive valuation member)⟩

/-- **The observer of the positive valuations does not separate `max 1 α` from
`α`.** -/
theorem positive_indistinguishable_max_one_var :
    (valuationObserver positiveValuations).Indistinguishable maxOneVar alpha :=
  (valuation_indistinguishable_max_one_var_iff _).mpr fun _ positive => positive 0

/-- The distinction that the observer of the positive valuations loses. -/
def positiveLostFiber : NonTrivialFiber (valuationReport positiveValuations) semanticReport where
  left := maxOneVar
  right := alpha
  sameShadow := valuationReport_eq_iff.mpr fun valuation positive =>
    (maxOneVar_eval_eq_iff valuation).mpr (positive 0)
  differentValue := fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same)

/-- The observer of the positive valuations is strictly coarser than the
semantic observer. -/
theorem positive_strictly_coarser_than_semantic :
    semanticObserver.Extends (valuationObserver positiveValuations) ∧
      ¬ (valuationObserver positiveValuations).Extends semanticObserver :=
  ⟨semantic_extends_valuation _, not_observer_extends_of_fiber positiveLostFiber⟩

/-- **The report at the positive valuations is a function of the normal-form
report of the paper's own rules**: at a valuation that is positive everywhere,
the value of a level is the value of the set that the paper's rules compute. -/
theorem positiveReport_factors_paperSet :
    Factors (normalSetWith addSubPaper unguardedLeaf) (valuationReport positiveValuations) :=
  ⟨fun set valuation => setEval valuation.1 set, fun level =>
    funext fun valuation => setEval_unguarded (addSubPaper_sound _) valuation.2 level⟩

/-- A distinction that (a) makes and that no positive valuation shows: the
pair that the rule on `Add` keeps apart. -/
def paperAddedOverPositiveFiber :
    NonTrivialFiber (valuationReport positiveValuations) (codeReport paperLevelTheory paperCode) where
  left := addPairLeft
  right := addPairRight
  sameShadow := valuationReport_eq_iff.mpr fun valuation _ => paper_add_incomplete.1 valuation
  differentValue := fun same => paper_add_incomplete.2 (codeReport_eq_iff.mp same)

/-- **Every distinction that (a) loses is at a valuation with a zero**: the
paper's code into the paper's level theory refines the observer of the positive
valuations, and strictly. -/
theorem paper_strictly_finer_than_positive :
    paperObserver.Extends (valuationObserver positiveValuations) ∧
      ¬ (valuationObserver positiveValuations).Extends paperObserver := by
  refine ⟨?_, not_observer_extends_of_fiber paperAddedOverPositiveFiber⟩
  rw [paperObserver_eq_normalForm]
  exact observer_extends_of_factors positiveReport_factors_paperSet

/-- The level variables of a level, in order of occurrence. -/
def LeanLevel.variables : LeanLevel → List Nat
  | .zero => []
  | .succ level => level.variables
  | .max first second => first.variables ++ second.variables
  | .imax first second => first.variables ++ second.variables
  | .param index => [index]

/-- **The value of a level depends on the values of its variables only.** -/
theorem LeanLevel.eval_congr :
    ∀ (level : LeanLevel) (first second : Nat → Nat),
      (∀ index ∈ level.variables, first index = second index) →
        level.eval first = level.eval second
  | .zero, _, _, _ => rfl
  | .succ level, first, second, agree => by
      have inner := LeanLevel.eval_congr level first second agree
      simp only [LeanLevel.eval, inner]
  | .max left right, first, second, agree => by
      have agreeLeft := LeanLevel.eval_congr left first second fun index member =>
        agree index (List.mem_append_left right.variables member)
      have agreeRight := LeanLevel.eval_congr right first second fun index member =>
        agree index (List.mem_append_right left.variables member)
      simp only [LeanLevel.eval, agreeLeft, agreeRight]
  | .imax left right, first, second, agree => by
      have agreeLeft := LeanLevel.eval_congr left first second fun index member =>
        agree index (List.mem_append_left right.variables member)
      have agreeRight := LeanLevel.eval_congr right first second fun index member =>
        agree index (List.mem_append_right left.variables member)
      simp only [LeanLevel.eval, agreeLeft, agreeRight]
  | .param index, _, _, agree => agree index (List.mem_singleton_self index)

/-- **Every distinction that (a) loses is at a valuation that gives the value
`0` to a variable of one of the two levels**: two levels whose codes the
paper's level theory converts have one value at every valuation that is
positive on their variables. -/
theorem eval_eq_of_conv_paperCode_on_variables {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second)) {valuation : Nat → Nat}
    (positive : ∀ index ∈ first.variables ++ second.variables, valuation index ≠ 0) :
    first.eval valuation = second.eval valuation := by
  have same : ∀ index ∈ first.variables ++ second.variables,
      valuation index = max 1 (valuation index) := fun index member => by
    have nonzero := positive index member
    omega
  rw [first.eval_congr valuation (fun index => max 1 (valuation index)) fun index member =>
      same index (List.mem_append_left _ member),
    second.eval_congr valuation (fun index => max 1 (valuation index)) fun index member =>
      same index (List.mem_append_right _ member)]
  exact eval_eq_of_conv_paperCode convertible fun index => by
    show max 1 (valuation index) ≠ 0
    omega

/-- The observer of the paper's code into the theory with explicit level
substitution: the empty guard of Definition 2 alone, the rule on `Add`
corrected. -/
noncomputable abbrev unguardedObserver : Tolerance LeanLevel := codeObserver leanTheoryExplicit paperCode

/-- **The empty guard alone is the observer of the positive valuations**: with
the rule on `Add` corrected, the paper's codes of two levels are convertible
exactly when the levels have one value at every valuation that is positive
everywhere, with any number of level variables. -/
theorem unguardedObserver_eq_positive : unguardedObserver = valuationObserver positiveValuations :=
  observer_eq_of_kernel fun _ _ =>
    codeReport_eq_iff.trans (conv_paperCode_explicit_iff_positive.trans valuationReport_eq_iff.symm)

/-- The empty guard alone is strictly coarser than the semantic observer. -/
theorem unguarded_strictly_coarser_than_semantic :
    semanticObserver.Extends unguardedObserver ∧ ¬ unguardedObserver.Extends semanticObserver := by
  rw [unguardedObserver_eq_positive]
  exact positive_strictly_coarser_than_semantic

/-- **The two defects of (a) are ordered**: the paper's own rule on `Add` only
adds distinctions to those of the empty guard.  The observer (a) refines the
observer of the empty guard alone, and strictly. -/
theorem paper_strictly_finer_than_unguarded :
    paperObserver.Extends unguardedObserver ∧ ¬ unguardedObserver.Extends paperObserver := by
  rw [unguardedObserver_eq_positive]
  exact paper_strictly_finer_than_positive

/-! ## The guard corrected alone -/

/-- The observer of the corrected code into the paper's level theory: each
level variable in its own guard, and the paper's rule on `Add`. -/
noncomputable abbrev guardedObserver : Tolerance LeanLevel := codeObserver paperLevelTheory code

/-- **The guard corrected alone is the crisp observer of the set computed with
the paper's `Add` and each variable in its own guard**, for all levels. -/
theorem guardedObserver_eq_normalForm :
    guardedObserver = observer (normalSetWith addSubPaper guardedLeaf) :=
  observer_eq_of_kernel fun _ _ => codeReport_eq_iff.trans conv_code_paperLevelTheory_iff

/-- The semantic report is a function of that set: the paper's rule on `Add`
loses no value. -/
theorem semanticReport_factors_guardedPaperSet :
    Factors (normalSetWith addSubPaper guardedLeaf) semanticReport :=
  ⟨fun set valuation => setEval valuation set, fun level =>
    funext fun valuation => setEval_guardedPaperSet valuation level⟩

/-- **The distinction that the guard corrected alone adds**:
`max 3 (max 1 (imax 2 α))` and `max 3 α` have one value at every valuation, and
codes that the paper's rule on `Add` keeps apart. -/
def guardedAddedFiber : NonTrivialFiber semanticReport (codeReport paperLevelTheory code) where
  left := guardPairLeft
  right := guardPairRight
  sameShadow := semanticReport_eq_iff.mpr guard_alone_incomplete.1
  differentValue := fun same => guard_alone_incomplete.2 (codeReport_eq_iff.mp same)

/-- **The guard corrected alone is strictly finer than the semantic
observer**: the paper's rule on `Add` loses no distinction, and adds some. -/
theorem guarded_strictly_finer_than_semantic :
    guardedObserver.Extends semanticObserver ∧ ¬ semanticObserver.Extends guardedObserver := by
  refine ⟨?_, not_observer_extends_of_fiber guardedAddedFiber⟩
  rw [guardedObserver_eq_normalForm]
  exact observer_extends_of_factors semanticReport_factors_guardedPaperSet

/-- **(a) and the guard corrected alone are incomparable, on equivalent
levels.**  With each variable in its own guard, the paper's rule on `Add`
separates `max 3 (max 1 (imax 2 α))` from `max 3 α`, which it joins under the
empty guard; under the empty guard it separates `max (succ α) (max 2 α)` from
`max 2 (succ α)`, which it joins once each variable is in its own guard.  The
pairs that the rule on `Add` fails to join depend on the guards: the two
defects of (a) are not independent. -/
theorem paper_incomparable_with_guarded :
    ¬ paperObserver.Extends guardedObserver ∧ ¬ guardedObserver.Extends paperObserver :=
  ⟨not_observer_extends_of_fiber
      { left := guardPairLeft
        right := guardPairRight
        sameShadow := codeReport_eq_iff.mpr (conv_paperCode_iff.mpr (by decide))
        differentValue := guardedAddedFiber.differentValue },
    not_observer_extends_of_fiber
      { left := addPairLeft
        right := addPairRight
        sameShadow := codeReport_eq_iff.mpr (conv_code_paperLevelTheory_iff.mpr (by decide))
        differentValue := paperAddedFiber.differentValue }⟩

/-! ## The preservation grades of the translations -/

/-- **The observer that a translation induces is the checker's observer of
terms, pulled back along the translation.** -/
theorem codeObserver_eq_pullback (theory : Theory) (translate : LeanLevel → Term) :
    codeObserver theory translate = (termObserver theory).pullback translate :=
  rfl

/-- **(c) changes no distance**: from the semantic observer of levels to the
checker's observer of terms, the repaired code has two-sided grade `1`. -/
theorem explicit_distortsAtMost_zero :
    Tolerance.DistortsAtMost semanticObserver (termObserver leanTheoryExplicit) code 0 :=
  (observer_distortsAtMost_zero_iff _ _ _).mpr fun _ _ =>
    semanticReport_eq_iff.trans (theorem2_all_levels.symm.trans conversionClass_eq_iff.symm)

/-- **(d) changes no distance.** -/
theorem frozen_distortsAtMost_zero :
    Tolerance.DistortsAtMost semanticObserver (termObserver frozenTheoryCorrected) (paperLevel frzVar) 0 :=
  (observer_distortsAtMost_zero_iff _ _ _).mpr fun _ _ =>
    semanticReport_eq_iff.trans
      (frozenCorrected_theorem2_all_levels.symm.trans conversionClass_eq_iff.symm)

/-- **(b) adds no distance and loses all of it**: every translation into the
paper's theory has one-sided grade `1`, as every collapse has, and two-sided
defect `1`. -/
theorem poly_grades (translate : LeanLevel → Term) :
    Tolerance.ExpandsAtMost semanticObserver (termObserver leanTheory) translate 0 ∧
      ∀ δ : ℚ, δ < 1 → ¬ Tolerance.DistortsAtMost semanticObserver (termObserver leanTheory) translate δ :=
  ⟨(observer_expandsAtMost_zero_iff _ _ _).mpr fun _ _ _ =>
      conversionClass_eq_iff.mpr (leanTheory_conv_all _ _),
    fun _ small => not_distortsAtMost_of_identified (first := .zero) (second := .succ .zero)
      (polyLostFiber translate).differentValue (conversionClass_eq_iff.mpr (leanTheory_conv_all _ _))
      small⟩

/-- **(a) has one-sided defect `1` and two-sided defect `1`**: the paper's code
adds a distance, between the levels of `paperAddedFiber`, and loses one,
between those of `paperLostFiber`. -/
theorem paper_grades :
    (∀ δ : ℚ, δ < 1 →
        ¬ Tolerance.ExpandsAtMost semanticObserver (termObserver paperLevelTheory) paperCode δ) ∧
      ∀ δ : ℚ, δ < 1 →
        ¬ Tolerance.DistortsAtMost semanticObserver (termObserver paperLevelTheory) paperCode δ :=
  ⟨fun _ small => not_expandsAtMost_of_separated paperAddedFiber.sameShadow
      paperAddedFiber.differentValue small,
    fun _ small => not_distortsAtMost_of_identified paperLostFiber.differentValue
      paperLostFiber.sameShadow small⟩

/-- **The empty guard alone adds no distance and loses one**: with the rule on
`Add` corrected, the paper's code has one-sided grade `1` and two-sided defect
`1`. -/
theorem unguarded_grades :
    Tolerance.ExpandsAtMost semanticObserver (termObserver leanTheoryExplicit) paperCode 0 ∧
      ∀ δ : ℚ, δ < 1 →
        ¬ Tolerance.DistortsAtMost semanticObserver (termObserver leanTheoryExplicit) paperCode δ :=
  ⟨(observer_expandsAtMost_zero_iff _ _ _).mpr fun _ _ same =>
      conversionClass_eq_iff.mpr (conv_paperCode_explicit_iff_positive.mpr fun valuation _ =>
        semanticReport_eq_iff.mp same valuation),
    fun _ small => not_distortsAtMost_of_identified (first := maxOneVar) (second := alpha)
      (fun same => maxOneVar_not_equiv (semanticReport_eq_iff.mp same))
      (conversionClass_eq_iff.mpr paperCode_max_one_var_conv_explicit) small⟩

/-- **The guard corrected alone adds a distance**: with the paper's rule on
`Add`, the corrected code has one-sided defect `1`, and so two-sided defect
`1`. -/
theorem guarded_grades :
    (∀ δ : ℚ, δ < 1 →
        ¬ Tolerance.ExpandsAtMost semanticObserver (termObserver paperLevelTheory) code δ) ∧
      ∀ δ : ℚ, δ < 1 →
        ¬ Tolerance.DistortsAtMost semanticObserver (termObserver paperLevelTheory) code δ :=
  have adds : ∀ δ : ℚ, δ < 1 →
      ¬ Tolerance.ExpandsAtMost semanticObserver (termObserver paperLevelTheory) code δ :=
    fun _ small => not_expandsAtMost_of_separated guardedAddedFiber.sameShadow
      guardedAddedFiber.differentValue small
  ⟨adds, fun δ small distorts => adds δ small distorts.expandsAtMost⟩

/-! ## The graded statements -/

/-- A value test satisfied by a level: at the valuation of the test, the level
has the value of the test. -/
def levelSat (level : LeanLevel) (test : (Nat → Nat) × Nat) : Prop := level.eval test.1 = test.2

/-- `max 1 α` and `α` disagree on a value test exactly when the test gives `α`
the value `0` and asks for the value `0` or `1`. -/
theorem levelSat_max_one_var_iff (test : (Nat → Nat) × Nat) :
    (levelSat maxOneVar test ↔ levelSat alpha test) ↔ ¬ (test.1 0 = 0 ∧ test.2 ≤ 1) := by
  simp only [levelSat, maxOneVar, alpha, LeanLevel.eval, eval_natLevel]
  omega

/-- **The tested distance between `max 1 α` and `α` is the weight of the tests
at `α = 0`**: for every finitely supported weighting of value tests, the two
levels agree outside a set of tests of mass `ε` exactly when the tests that give
`α` the value `0` and ask for `0` or `1` have mass at most `ε`. -/
theorem withinTest_max_one_var_iff (ν : SentenceWeighting ((Nat → Nat) × Nat)) (ε : ℚ) :
    WithinTest levelSat ν maxOneVar alpha ε ↔
      ν.mass (ν.support.filter fun test => test.1 0 = 0 ∧ test.2 ≤ 1) ≤ ε := by
  constructor
  · rintro ⟨disagreement, inside, agree, small⟩
    refine le_trans (ν.mass_mono inside fun test member => ?_) small
    rw [Finset.mem_filter] at member
    by_contra outside
    exact (levelSat_max_one_var_iff test).mp (agree test member.1 outside) member.2
  · intro small
    refine ⟨_, Finset.filter_subset _ _, fun test member outside => ?_, small⟩
    rw [Finset.mem_filter, not_and] at outside
    exact (levelSat_max_one_var_iff test).mpr (outside member)

/-- **Every pair that (a) identifies is within the mass of the tests that give
the value `0` to one of its variables**: for every finitely supported weighting
of value tests, two levels whose codes the paper's level theory converts agree
on every test whose valuation is positive on the variables of the two levels. -/
theorem paper_withinTest {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second))
    (ν : SentenceWeighting ((Nat → Nat) × Nat)) :
    WithinTest levelSat ν first second
      (ν.mass (ν.support.filter fun test =>
        ∃ index ∈ first.variables ++ second.variables, test.1 index = 0)) := by
  refine ⟨_, Finset.filter_subset _ _, fun test member outside => ?_, le_refl _⟩
  rw [Finset.mem_filter, not_and] at outside
  have positive : ∀ index ∈ first.variables ++ second.variables, test.1 index ≠ 0 :=
    fun index occurs zero => outside member ⟨index, occurs, zero⟩
  unfold levelSat
  rw [eval_eq_of_conv_paperCode_on_variables convertible positive]

open Classical in
/-- **The distance between `max 1 α` and `α` in the weighted tolerance of value
tests**: for every weighting of value tests of total mass at most one, the
graded observer that it defines puts the two levels at the distance that is
the mass of the tests that give `α` the value `0` and ask for `0` or `1`. -/
theorem testTolerance_distance_max_one_var (ν : SentenceWeighting ((Nat → Nat) × Nat))
    (total : ν.mass ν.support ≤ 1) :
    (testTolerance levelSat total).distance maxOneVar alpha =
      ν.mass (ν.support.filter fun test => test.1 0 = 0 ∧ test.2 ≤ 1) := by
  rw [testTolerance_distance]
  exact le_antisymm
    (withinTest_iff_testDistance_le.mp ((withinTest_max_one_var_iff ν _).mpr le_rfl))
    ((withinTest_max_one_var_iff ν _).mp (withinTest_iff_testDistance_le.mpr le_rfl))

open Classical in
/-- **In the weighted tolerance of value tests, two levels that (a) identifies
are no further apart than the mass of the tests that give the value `0` to one
of their variables.** -/
theorem paper_testTolerance_distance_le {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second))
    (ν : SentenceWeighting ((Nat → Nat) × Nat)) (total : ν.mass ν.support ≤ 1) :
    (testTolerance levelSat total).distance first second ≤
      ν.mass (ν.support.filter fun test =>
        ∃ index ∈ first.variables ++ second.variables, test.1 index = 0) := by
  rw [testTolerance_distance]
  exact withinTest_iff_testDistance_le.mp (paper_withinTest convertible ν)

open Classical in
/-- **A weighted observer that tests only at valuations positive on the
variables of two levels does not separate them when (a) identifies them.** -/
theorem paper_testTolerance_indistinguishable {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second))
    (ν : SentenceWeighting ((Nat → Nat) × Nat)) (total : ν.mass ν.support ≤ 1)
    (positive : ∀ test ∈ ν.support, ∀ index ∈ first.variables ++ second.variables,
      test.1 index ≠ 0) :
    (testTolerance levelSat total).Indistinguishable first second :=
  (testTolerance_indistinguishable_iff total).mpr fun test member => by
    unfold levelSat
    rw [eval_eq_of_conv_paperCode_on_variables convertible
      (positive test (Finset.mem_coe.mp member))]

/-- A level equation holds at a valuation. -/
def equationSat (valuation : Nat → Nat) (equation : LeanLevel × LeanLevel) : Prop :=
  equation.1.eval valuation = equation.2.eval valuation

/-- The equation `max 1 α = α` holds at every positive valuation. -/
theorem max_one_var_validated_by_positive :
    (maxOneVar, alpha) ∈ consequencesIn equationSat positiveValuations ∅ :=
  fun valuation member => (maxOneVar_eval_eq_iff valuation).mpr (member.1 0)

/-- **Every equation that (a) validates holds at every positive valuation**:
the equations that the paper's level theory adds to Lean's are consequences of
the positive valuations. -/
theorem paper_validated_by_positive {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second)) :
    (first, second) ∈ consequencesIn equationSat positiveValuations ∅ :=
  fun _ member => eval_eq_of_conv_paperCode convertible member.1

/-- **The empty guard alone validates exactly the consequences of the positive
valuations**: with the rule on `Add` corrected, the paper's codes of two levels
are convertible exactly when the equation between them holds at every positive
valuation. -/
theorem unguarded_validated_iff_positive {first second : LeanLevel} :
    Conv leanTheoryExplicit (paperCode first) (paperCode second) ↔
      (first, second) ∈ consequencesIn equationSat positiveValuations ∅ :=
  ⟨fun convertible _ member => eval_eq_of_conv_paperCode_explicit convertible member.1,
    fun validated => conv_paperCode_explicit_iff_positive.mpr fun _ positive =>
      validated ⟨positive, fun _ member => absurd member (Set.notMem_empty _)⟩⟩

/-- **The leak of the positive valuations**: if the positive valuations host
the level semantics up to `ε` for a weighting that tests the equation
`max 1 α = α`, then `ε` is at least the weight of that equation. -/
theorem positive_hosting_weight_le {ν : SentenceWeighting (LeanLevel × LeanLevel)} {ε : ℚ}
    (hosts : EpsHosts equationSat ν positiveValuations ∅ ε)
    (tested : (maxOneVar, alpha) ∈ ν.support) : ν.weight (maxOneVar, alpha) ≤ ε :=
  weight_le_of_leak hosts tested max_one_var_validated_by_positive (m := fun _ => 0)
    (fun _ member => absurd member (Set.notMem_empty _))
    (fun same => (maxOneVar_eval_eq_iff fun _ => 0).mp same rfl)

/-- **For the weighting that tests the equation `max 1 α = α` alone, the
positive valuations host the level semantics up to `ε` exactly when `ε` is at
least the weight of the equation.** -/
theorem positive_hosting_single_iff {weight : ℚ} (positive : 0 < weight) (ε : ℚ) :
    EpsHosts equationSat ⟨{(maxOneVar, alpha)}, fun _ => weight, fun _ _ => positive⟩
        positiveValuations ∅ ε ↔ weight ≤ ε := by
  constructor
  · intro hosts
    exact positive_hosting_weight_le hosts (Finset.mem_singleton_self _)
  · intro small
    rw [epsHosts_iff]
    intro valuation _
    refine ⟨fun _ => 1, ⟨fun _ => Nat.one_ne_zero, fun _ member => absurd member (Set.notMem_empty _)⟩,
      {(maxOneVar, alpha)}, Finset.Subset.refl _, fun equation member outside => absurd member outside, ?_⟩
    simpa [SentenceWeighting.mass] using small

/-! ## The translations as maps of theories -/

/-- **The levels of a collection, as a theory given by its terms**: compared
by Lean's equivalence of levels, with no reduction. -/
def levelsWhere (keep : LeanLevel → Prop) : GSLT.{0} :=
  GSLT.equationOnly ({level : LeanLevel // keep level}) (⟨fun first second => LeanLevel.Equiv first.1 second.1,
        ⟨fun _ _ => rfl, fun related valuation => (related valuation).symm,
          fun first second valuation => (first valuation).trans (second valuation)⟩⟩)

/-- **A translation of the levels of a collection that respects their
equivalence, as a map of theories** into the conversion presentation of its
target. -/
def translationMap (theory : Theory) (keep : LeanLevel → Prop) (translate : LeanLevel → Term)
    (respects : ∀ first second : LeanLevel, keep first → keep second →
      LeanLevel.Equiv first second → Conv theory (translate first) (translate second)) :
    ContextMap (levelsWhere keep).termsAlone (conversionTheory theory) :=
  ContextMap.ofTerms () (fun level => translate level.1)
    (fun {first second} equivalent => respects first.1 second.1 first.2 second.2 equivalent)

/-- **A translation is hosting exactly when it reflects the equivalence of
levels**: neither theory has a reduction to preserve or to reflect. -/
theorem translationMap_hosting_iff (theory : Theory) (keep : LeanLevel → Prop)
    (translate : LeanLevel → Term)
    (respects : ∀ first second : LeanLevel, keep first → keep second →
      LeanLevel.Equiv first second → Conv theory (translate first) (translate second)) :
    (translationMap theory keep translate respects).Hosting ↔
      ∀ first second : LeanLevel, keep first → keep second →
        Conv theory (translate first) (translate second) → LeanLevel.Equiv first second := by
  refine (ContextMap.ofTerms_hosting_iff (source := levelsWhere keep) (target := conversionTheory theory)
    () (fun level => translate level.1)
    (fun {first second} equivalent => respects first.1 second.1 first.2 second.2 equivalent)).trans
    ⟨?_, ?_⟩
  · rintro ⟨reflects, _, _⟩ first second keepFirst keepSecond convertible
    exact reflects ⟨first, keepFirst⟩ ⟨second, keepSecond⟩ convertible
  · intro reflects
    exact ⟨fun first second convertible => reflects first.1 second.1 first.2 second.2 convertible,
      fun _ _ step => step.elim, fun _ _ step => step.elim⟩

/-- **Being a map is the semantic observer refining the observer of the code**,
on the collection: a translation respects the equivalence of the levels of a
collection exactly when, restricted to it, the semantic observer refines the
observer that the translation induces. -/
theorem respects_iff_semantic_extends (theory : Theory) (keep : LeanLevel → Prop)
    (translate : LeanLevel → Term) :
    (∀ first second : LeanLevel, keep first → keep second → LeanLevel.Equiv first second →
        Conv theory (translate first) (translate second)) ↔
      (semanticObserver.pullback (Subtype.val : {level : LeanLevel // keep level} → LeanLevel)).Extends
        ((codeObserver theory translate).pullback Subtype.val) := by
  rw [pullback_observer, pullback_observer, observer_extends_iff]
  exact ⟨fun respects first second same =>
      codeReport_eq_iff.mpr (respects first.1 second.1 first.2 second.2 (semanticReport_eq_iff.mp same)),
    fun sound first second keepFirst keepSecond equivalent =>
      codeReport_eq_iff.mp (sound ⟨first, keepFirst⟩ ⟨second, keepSecond⟩
        (semanticReport_eq_iff.mpr equivalent))⟩

/-- **Hosting is the observer of the code refining the semantic observer**, on
the collection. -/
theorem translationMap_hosting_iff_extends (theory : Theory) (keep : LeanLevel → Prop)
    (translate : LeanLevel → Term)
    (respects : ∀ first second : LeanLevel, keep first → keep second →
      LeanLevel.Equiv first second → Conv theory (translate first) (translate second)) :
    (translationMap theory keep translate respects).Hosting ↔
      ((codeObserver theory translate).pullback
          (Subtype.val : {level : LeanLevel // keep level} → LeanLevel)).Extends
        (semanticObserver.pullback Subtype.val) := by
  rw [translationMap_hosting_iff, pullback_observer, pullback_observer, observer_extends_iff]
  exact ⟨fun reflects first second same =>
      semanticReport_eq_iff.mpr (reflects first.1 second.1 first.2 second.2 (codeReport_eq_iff.mp same)),
    fun sound first second keepFirst keepSecond convertible =>
      semanticReport_eq_iff.mp (sound ⟨first, keepFirst⟩ ⟨second, keepSecond⟩
        (codeReport_eq_iff.mpr convertible))⟩

/-! ### (c) and (d): hosting maps on every collection of levels -/

/-- **(c) as a map of theories**: the repaired code of the levels of a
collection, into the conversion presentation of the theory with explicit level
substitution. -/
def explicitCodeMap (keep : LeanLevel → Prop) :
    ContextMap (levelsWhere keep).termsAlone (conversionTheory leanTheoryExplicit) :=
  translationMap leanTheoryExplicit keep code fun _ _ _ _ equivalent => theorem3_all_levels equivalent

/-- **(c) is a hosting map on every collection of levels.** -/
theorem explicitCodeMap_hosting (keep : LeanLevel → Prop) : (explicitCodeMap keep).Hosting :=
  (translationMap_hosting_iff _ _ _ _).mpr fun _ _ _ _ convertible => equiv_of_conv_code convertible

/-- **(c) is not exhausting**: the target has terms that are the code of no
level, a sort for one. -/
theorem explicitCodeMap_not_exhausting (keep : LeanLevel → Prop) :
    ¬ (explicitCodeMap keep).Exhausting := by
  intro exhausting
  obtain ⟨preimage, convertible⟩ :=
    ContextMap.Exhausting.term_surjective (explicitCodeMap keep) exhausting (origin := PUnit.unit)
      (Term.srt .type)
  have rigid : ∀ name ∈ setConstructors, ¬ leanTheoryExplicit.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have reduces : Reduces leanTheoryExplicit (code preimage.1) (normalCode (normalSet preimage.1)) :=
    (code_reduces_normalSet preimage.1).mono pureTheoryExplicit_extends
  exact not_conv_of_normal leanTheoryExplicit_confluent (srt_normal leanTheoryExplicit_headed .type)
    (normalCode_normal leanTheoryExplicit_headed rigid _) (by simp [normalCode, ap, apT])
    (.trans _ _ _ (conversionTheory_equations.mp convertible) reduces.conv)

/-- **(d) as a map of theories**: the frozen-parameter code of the levels of a
collection, into the conversion presentation of the frozen strategy over the
corrected rules. -/
def frozenCodeMap (keep : LeanLevel → Prop) :
    ContextMap (levelsWhere keep).termsAlone (conversionTheory frozenTheoryCorrected) :=
  translationMap frozenTheoryCorrected keep (paperLevel frzVar) fun _ _ _ _ equivalent =>
    frozenCorrected_theorem2_all_levels.mpr equivalent

/-- **(d) is a hosting map on every collection of levels.** -/
theorem frozenCodeMap_hosting (keep : LeanLevel → Prop) : (frozenCodeMap keep).Hosting :=
  (translationMap_hosting_iff _ _ _ _).mpr fun _ _ _ _ convertible =>
    frozenCorrected_theorem2_all_levels.mp convertible

/-- **(d) is not exhausting**: a sort is the frozen-parameter code of no
level. -/
theorem frozenCodeMap_not_exhausting (keep : LeanLevel → Prop) :
    ¬ (frozenCodeMap keep).Exhausting := by
  intro exhausting
  obtain ⟨preimage, convertible⟩ :=
    ContextMap.Exhausting.term_surjective (frozenCodeMap keep) exhausting (origin := PUnit.unit)
      (Term.srt .type)
  have headed : frozenTheoryCorrected.Headed := frozenTheoryCorrected_orthogonal.leftAlgebraic.headed
  have rigid : ∀ name ∈ setConstructors, ¬ frozenTheoryCorrected.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have reduces : Reduces frozenTheoryCorrected (paperLevel frzVar preimage.1)
      (normalCode (normalSet preimage.1)) :=
    (frozenCorrected_reduces_code preimage.1).trans
      ((code_reduces_normalSet preimage.1).mono pureTheoryExplicit_extends_frozenCorrected)
  exact not_conv_of_normal frozenTheoryCorrected_confluent (srt_normal headed .type)
    (normalCode_normal headed rigid _) (by simp [normalCode, ap, apT])
    (.trans _ _ _ (conversionTheory_equations.mp convertible) reduces.conv)

/-! ### (a): not a map, and not hosting where it is one -/

/-- **(a) is not a map of theories**: no map from the levels, compared by
their equivalence, into the conversion presentation of the paper's level
theory has the paper's code as its map on terms. -/
theorem paperCode_not_a_map :
    ¬ ∃ map : ContextMap (levelsWhere fun _ => True).termsAlone (conversionTheory paperLevelTheory),
        ∀ level : (levelsWhere fun _ => True).Term,
          map.term (origin := PUnit.unit) level = paperCode level.1 := by
  rintro ⟨map, isCode⟩
  have respected : Conv paperLevelTheory (map.term (origin := PUnit.unit) ⟨addPairLeft, trivial⟩)
      (map.term (origin := PUnit.unit) ⟨addPairRight, trivial⟩) :=
    map.term_resp (origin := PUnit.unit) (first := ⟨addPairLeft, trivial⟩)
      (second := ⟨addPairRight, trivial⟩) addPair_equiv
  exact paper_add_incomplete.2 ((congrArg₂ (Conv paperLevelTheory) (isCode ⟨addPairLeft, trivial⟩)
    (isCode ⟨addPairRight, trivial⟩)).mp respected)

/-- **Where (a) is a map, it is not hosting**: on every collection that holds
`max 1 α` and `α`, a map of theories whose map on terms is the paper's code
identifies two levels that are apart. -/
theorem paperCode_not_hosting {keep : LeanLevel → Prop} (hasMax : keep maxOneVar) (hasVar : keep alpha)
    (map : ContextMap (levelsWhere keep).termsAlone (conversionTheory paperLevelTheory))
    (isCode : ∀ level : (levelsWhere keep).Term,
      map.term (origin := PUnit.unit) level = paperCode level.1) : ¬ map.Hosting := by
  have identified : Conv paperLevelTheory (map.term (origin := PUnit.unit) ⟨maxOneVar, hasMax⟩)
      (map.term (origin := PUnit.unit) ⟨alpha, hasVar⟩) :=
    (congrArg₂ (Conv paperLevelTheory) (isCode ⟨maxOneVar, hasMax⟩) (isCode ⟨alpha, hasVar⟩)).mpr
      paperLevelTheory_max_one_var_reduces.conv
  exact ContextMap.not_hosting_of_identifies map (origin := PUnit.unit)
    (first := ⟨maxOneVar, hasMax⟩) (second := ⟨alpha, hasVar⟩) maxOneVar_not_equiv identified

/-! ### (b): every translation is a map, and none is hosting -/

/-- **(b) as a map of theories**: every translation of the levels of a
collection is a map into the conversion presentation of the paper's theory,
whose conversion relates every two terms. -/
def polyMap (keep : LeanLevel → Prop) (translate : LeanLevel → Term) :
    ContextMap (levelsWhere keep).termsAlone (conversionTheory leanTheory) :=
  translationMap leanTheory keep translate fun _ _ _ _ _ => leanTheory_conv_all _ _

/-- **No map into the paper's theory is hosting**, from a collection with two
levels that are not equivalent: all the terms of the target are identified. -/
theorem poly_not_hosting {keep : LeanLevel → Prop}
    (map : ContextMap (levelsWhere keep).termsAlone (conversionTheory leanTheory))
    {first second : LeanLevel} (keepFirst : keep first) (keepSecond : keep second)
    (distinct : ¬ LeanLevel.Equiv first second) : ¬ map.Hosting :=
  not_hosting_into_total_of_apart (fun _ _ _ => conversionTheory_equations.mpr (leanTheory_conv_all _ _))
    map (origin := PUnit.unit) (first := ⟨first, keepFirst⟩) (second := ⟨second, keepSecond⟩) distinct

/-- **(b) is hosting exactly on the collections whose levels are all
equivalent.** -/
theorem polyMap_hosting_iff (keep : LeanLevel → Prop) (translate : LeanLevel → Term) :
    (polyMap keep translate).Hosting ↔
      ∀ first second : LeanLevel, keep first → keep second → LeanLevel.Equiv first second :=
  (translationMap_hosting_iff _ _ _ _).trans
    ⟨fun reflects first second keepFirst keepSecond =>
        reflects first second keepFirst keepSecond (leanTheory_conv_all _ _),
      fun equivalent first second keepFirst keepSecond _ => equivalent first second keepFirst keepSecond⟩

/-! ## Typing as an observer: the rule on `PUnit.rec` -/

/-- The rule on `PUnit.rec` contracts `PUnit.rec.{1, 0} Q h x` to `h`. -/
theorem punitRedex_step : Step leanTheoryExplicit punitRedex (.var 1) := by
  have member : leanTheoryExplicit.rule punitRecRuleExplicit := by
    show punitRecRuleExplicit ∈ explicitRules
    decide +kernel
  exact Step.root (rootStep_of_instance member
    (assign [instAt [levelOne, levelZero], .var 2, .var 1, .var 0]) (by decide +kernel)
    (by decide +kernel))

/-- The minor premise `h : Q PUnit.unit` has not the type `ε |0| (Q x)` of the
redex `PUnit.rec Q h x`: the two types are distinct normal forms. -/
theorem punitMinor_not_typed :
    ¬ LambdaPiModulo leanTheoryExplicit punitContext (.var 1) punitRedexType := by
  intro reductTyped
  have declared : LambdaPiModulo leanTheoryExplicit punitContext (.var 1)
      (eps levelZero (.app (.var 2) unitValueExplicit)) := .var rfl
  have convertible := HasType.unique Example.standardLF_functional leanTheoryExplicit_confluent
    leanTheoryExplicit_headed leanTheoryExplicit_closedBodies (.var 1) declared reductTyped
  exact not_conv_of_normal leanTheoryExplicit_confluent
    (normalExplicit_of_stepOnce (by decide +kernel)) (normalExplicit_of_stepOnce (by decide +kernel))
    (by decide) convertible

/-- **Reduction is visible to the typing observer**: in the theory with
explicit level substitution, the typed term `PUnit.rec Q h x` steps to `h`,
and the typing observer of its type puts the two apart. -/
theorem punitRec_step_apart_for_typing :
    LambdaPiModulo leanTheoryExplicit punitContext punitRedex punitRedexType ∧
      Step leanTheoryExplicit punitRedex (.var 1) ∧
      (observer (typingReport leanTheoryExplicit punitContext punitRedexType)).Apart
        punitRedex (.var 1) := by
  refine ⟨punitRedex_typed, punitRedex_step, ?_⟩
  by_contra notApart
  exact punitMinor_not_typed ((typing_indistinguishable_iff punitRedex_typed).mp
    ((Tolerance.not_apart_iff_indistinguishable _ _ _).mp notApart))

/-- **The inhabitants of `ε |0| (Q x)` are not hosted by the calculus as it
runs**: the transcribed rule on `PUnit.rec` gives the image of an inhabitant a
step that comes from no step between inhabitants. -/
theorem punitRec_forgetTyping_not_hosting :
    ¬ (forgetTyping leanTheoryExplicit punitContext punitRedexType).Hosting := fun hosting =>
  punitMinor_not_typed
    ((forgetTyping_hosting_iff _ _ _).mp hosting _ _ punitRedex_typed punitRedex_step)

#print axioms not_hosting_into_total_of_apart
#print axioms observer_eq_of_kernel
#print axioms observer_extends_iff
#print axioms not_observer_extends_of_fiber
#print axioms typing_indistinguishable_iff
#print axioms forgetTyping_hosting_iff
#print axioms semantic_extends_valuation
#print axioms valuationObserver_anti
#print axioms valuationObserver_univ
#print axioms paperLevelTheory_max_one_var_reduces
#print axioms paperLostFiber
#print axioms paperAddedFiber
#print axioms paper_incomparable_with_semantic
#print axioms paperObserver_eq_normalForm
#print axioms transcribed_not_extends_semantic
#print axioms codeObserver_leanTheory_eq_top
#print axioms polyObserver_eq_top
#print axioms polyLostFiber
#print axioms poly_strictly_coarser_than_semantic
#print axioms orderedCodeObserver_lean_eq_top
#print axioms orderedCodeObserver_eq_of_orthogonal
#print axioms explicitObserver_eq_normalForm
#print axioms semanticReport_factors_normalSet
#print axioms normalSet_factors_semanticReport
#print axioms explicitObserver_eq_semantic
#print axioms explicitObserver_in_declaration_eq_semantic
#print axioms frozenObserver_eq_explicit
#print axioms frozenCorrected_theorem2_all_levels
#print axioms frozenObserver_eq_semantic
#print axioms frozenPaper_incomparable_with_semantic
#print axioms valuation_indistinguishable_max_one_var_iff
#print axioms positive_indistinguishable_max_one_var
#print axioms positive_strictly_coarser_than_semantic
#print axioms positiveReport_factors_paperSet
#print axioms paper_strictly_finer_than_positive
#print axioms LeanLevel.eval_congr
#print axioms eval_eq_of_conv_paperCode_on_variables
#print axioms unguardedObserver_eq_positive
#print axioms unguarded_strictly_coarser_than_semantic
#print axioms paper_strictly_finer_than_unguarded
#print axioms guardedObserver_eq_normalForm
#print axioms guardedAddedFiber
#print axioms guarded_strictly_finer_than_semantic
#print axioms paper_incomparable_with_guarded
#print axioms observer_expandsAtMost_zero_iff
#print axioms not_expandsAtMost_of_separated
#print axioms observer_distortsAtMost_zero_iff
#print axioms not_distortsAtMost_of_identified
#print axioms explicit_distortsAtMost_zero
#print axioms frozen_distortsAtMost_zero
#print axioms poly_grades
#print axioms paper_grades
#print axioms unguarded_grades
#print axioms guarded_grades
#print axioms withinTest_max_one_var_iff
#print axioms paper_withinTest
#print axioms testTolerance_distance_max_one_var
#print axioms paper_testTolerance_distance_le
#print axioms paper_testTolerance_indistinguishable
#print axioms paper_validated_by_positive
#print axioms unguarded_validated_iff_positive
#print axioms positive_hosting_weight_le
#print axioms positive_hosting_single_iff
#print axioms translationMap_hosting_iff
#print axioms respects_iff_semantic_extends
#print axioms translationMap_hosting_iff_extends
#print axioms explicitCodeMap_hosting
#print axioms explicitCodeMap_not_exhausting
#print axioms frozenCodeMap_hosting
#print axioms frozenCodeMap_not_exhausting
#print axioms paperCode_not_a_map
#print axioms paperCode_not_hosting
#print axioms poly_not_hosting
#print axioms polyMap_hosting_iff
#print axioms punitMinor_not_typed
#print axioms punitRec_step_apart_for_typing
#print axioms punitRec_forgetTyping_not_hosting

end Mettapedia.GSLT.Dedukti.LeanMinus
