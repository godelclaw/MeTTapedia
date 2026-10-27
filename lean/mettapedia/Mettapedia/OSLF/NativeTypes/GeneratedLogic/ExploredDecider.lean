import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.MuEmbedding
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution
import Mettapedia.OSLF.NativeTypes.Executable.ExploredCompiled

/-!
# Explored graphs as a certified decider

An explored graph decides a future μ-calculus formula with atoms at a well-sorted start of a compiled root plan, read
through an abstraction that loses no answer: the reachable states may be infinite, and the abstraction's classes
finitely many. Its verdicts become front-door answers.

- **Transfer between spans** (`satisfies_transfer`): two reduction spans with the same steps between good states,
  closed under the steps of both, satisfy the same future formulas with positive fixed points at good states.
- **The compiled root plan's steps are the reference steps** between well-sorted states, for a root-profile language
  whose rules are aligned (`plan_steps_agree`).
- **A query** (`Query`) is a μ-calculus formula over traversals with atoms, a generated formula for each atom, and an
  abstraction; its generated formula is the formula's embedding with the atoms' formulas in place (`Query.native`).
  A valid query (`Query.Valid`) has a root-profile language, an abstraction meeting the explorer's conditions, positive
  fixed points, and atoms that hold exactly where their formulas do.
- **The decider** (`decider`) answers a query's generated formula at a well-sorted term with the explored graph's
  verdict, exactly (`decides_exact`); asked through `askWith`, its answers are front-door answers with the evidence
  `decided`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredDecider

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.Logic.ModalMuCalculus (satisfies satisfies_congr)
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan)
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula (Traversal transitionSystem pullEnvironment satisfies_pullback)
open Mettapedia.OSLF.NativeTypes.Executable.Explored (Atoms FutureOnly ForwardClosed restrict inclusion
  inclusion_sourceLifts covers_of_futureOnly)
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled (theory verdict Abstraction verdict_proved verdict_refuted)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan RootProfile)
open Mettapedia.OSLF.Framework.HerbrandBridge (Sorted compiled_steps_agree sorted_closed language_sorted_closed)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Embeddings (ofMu muConsistent traversal sat_ofMu realizes_transitionSystem)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted checkOpenPatternWellSorted_eq_true_iff)

/-! ## Transfer between spans -/

/-- **Two spans with the same steps between good states, closed under both, satisfy the same future formulas at good
states.** -/
theorem satisfies_transfer {X : Type} {first second : ReductionSpan.{0, 0} X} (good : X → Prop)
    (firstClosed : ForwardClosed first good) (secondClosed : ForwardClosed second good)
    (agree : ∀ source target, good source → good target →
      ((∃ event : first.Edge, first.source event = source ∧ first.target event = target) ↔
        ∃ event : second.Edge, second.source event = source ∧ second.target event = target))
    {n : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal n) (future : FutureOnly formula = true)
    (positive : fixedPointsPositive formula = true) (env : Mettapedia.Logic.ModalMuCalculus.Env X n) {state : X}
    (stateGood : good state) :
    satisfies (transitionSystem first) env formula state ↔ satisfies (transitionSystem second) env formula state := by
  have viaFirst := satisfies_pullback (inclusion first good) formula
    (covers_of_futureOnly _ (inclusion_sourceLifts firstClosed) formula future) positive env ⟨state, stateGood⟩
  have viaSecond := satisfies_pullback (inclusion second good) formula
    (covers_of_futureOnly _ (inclusion_sourceLifts secondClosed) formula future) positive env ⟨state, stateGood⟩
  refine viaFirst.trans (Iff.trans ?_ viaSecond.symm)
  refine satisfies_congr (fun source direction target => ?_) (fun _ _ => Iff.rfl) formula _
  cases direction
  · constructor
    · rintro ⟨⟨event, sourceGood, targetGood⟩, starts, ends⟩
      obtain ⟨matched, matchedSource, matchedTarget⟩ :=
        (agree _ _ source.2 target.2).mp ⟨event, congrArg Subtype.val starts, congrArg Subtype.val ends⟩
      exact ⟨⟨matched, matchedSource ▸ source.2, matchedTarget ▸ target.2⟩, Subtype.ext matchedSource,
        Subtype.ext matchedTarget⟩
    · rintro ⟨⟨event, sourceGood, targetGood⟩, starts, ends⟩
      obtain ⟨matched, matchedSource, matchedTarget⟩ :=
        (agree _ _ source.2 target.2).mpr ⟨event, congrArg Subtype.val starts, congrArg Subtype.val ends⟩
      exact ⟨⟨matched, matchedSource ▸ source.2, matchedTarget ▸ target.2⟩, Subtype.ext matchedSource,
        Subtype.ext matchedTarget⟩
  · constructor
    · rintro ⟨⟨event, sourceGood, targetGood⟩, ends, starts⟩
      obtain ⟨matched, matchedSource, matchedTarget⟩ :=
        (agree _ _ target.2 source.2).mp ⟨event, congrArg Subtype.val starts, congrArg Subtype.val ends⟩
      exact ⟨⟨matched, matchedSource ▸ target.2, matchedTarget ▸ source.2⟩, Subtype.ext matchedTarget,
        Subtype.ext matchedSource⟩
    · rintro ⟨⟨event, sourceGood, targetGood⟩, ends, starts⟩
      obtain ⟨matched, matchedSource, matchedTarget⟩ :=
        (agree _ _ target.2 source.2).mpr ⟨event, congrArg Subtype.val starts, congrArg Subtype.val ends⟩
      exact ⟨⟨matched, matchedSource ▸ target.2, matchedTarget ▸ source.2⟩, Subtype.ext matchedTarget,
        Subtype.ext matchedSource⟩

/-! ## The compiled root plan and the reference steps -/

variable {relEnv : RelationEnv} {language : LanguageDef} {type : TypeExpr}

theorem isState_of_sorted {pattern : Pattern} (sorted : Sorted language type pattern) : IsState pattern :=
  ⟨sorted.2.2.2, sorted.2.2.1⟩

/-- **Between well-sorted states, the compiled root plan's steps are the reference steps.** -/
theorem plan_steps_agree (root : RootProfile language type) (aligned : ReferenceProfile language) {source target : Pattern}
    (sourceSorted : Sorted language type source) (targetSorted : Sorted language type target) :
    (∃ event : (gsltSpan (theory (rootPlan language) [] type)).Edge,
        (gsltSpan (theory (rootPlan language) [] type)).source event = source ∧
          (gsltSpan (theory (rootPlan language) [] type)).target event = target) ↔
      ∃ event : (HigherOrder.stepSpan (referenceStructure relEnv language)).Edge,
        (HigherOrder.stepSpan (referenceStructure relEnv language)).source event = source ∧
          (HigherOrder.stepSpan (referenceStructure relEnv language)).target event = target := by
  rw [compiled_steps_agree root sourceSorted]
  constructor
  · rintro ⟨⟨⟨_, _⟩, member⟩, rfl, rfl⟩
    exact ⟨⟨_, (step_iff_rootReducts root.equationFree aligned root.unconditional rfl).mpr
      ⟨isState_of_sorted sourceSorted, isState_of_sorted targetSorted, member⟩⟩, rfl, rfl⟩
  · rintro ⟨⟨⟨_, _⟩, step⟩, rfl, rfl⟩
    exact ⟨⟨_, ((step_iff_rootReducts root.equationFree aligned root.unconditional rfl).mp step).2.2⟩, rfl, rfl⟩

/-- Reference steps from well-sorted states end at well-sorted states. -/
theorem reference_sorted_closed (root : RootProfile language type) (aligned : ReferenceProfile language) :
    ForwardClosed (HigherOrder.stepSpan (referenceStructure relEnv language)) (Sorted language type) := by
  rintro ⟨⟨source, target⟩, step⟩ sourceSorted
  exact language_sorted_closed root ⟨(source, target),
    ((step_iff_rootReducts root.equationFree aligned root.unconditional rfl).mp step).2.2⟩ sourceSorted

/-- **The runs of a first-order language between object states are its reference steps**, as transition systems. -/
theorem runs_transitions_agree (free : language.isEquationFree = true) (aligned : ReferenceProfile language)
    (unconditional : Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction.isUnconditionalAligned language = true)
    (source : Pattern) (direction : Traversal) (target : Pattern) :
    (transitionSystem (Mettapedia.OSLF.Framework.BackwardSearch.between
        (Mettapedia.OSLF.Framework.HerbrandBridge.languageSpan language)
        Mettapedia.OSLF.Framework.FiniteModels.ObjectState)).trans source direction target ↔
      (transitionSystem (HigherOrder.stepSpan (referenceStructure relEnv language))).trans source direction target := by
  cases direction
  · constructor
    · rintro ⟨⟨⟨⟨first, second⟩, member⟩, sourceState, targetState⟩, rfl, rfl⟩
      exact ⟨⟨(first, second), (step_iff_rootReducts free aligned unconditional rfl).mpr
        ⟨sourceState, targetState, member⟩⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨_, _⟩, step⟩, rfl, rfl⟩
      obtain ⟨sourceState, targetState, member⟩ := (step_iff_rootReducts free aligned unconditional rfl).mp step
      exact ⟨⟨⟨⟨_, _⟩, member⟩, sourceState, targetState⟩, rfl, rfl⟩
  · constructor
    · rintro ⟨⟨⟨⟨first, second⟩, member⟩, sourceState, targetState⟩, rfl, rfl⟩
      exact ⟨⟨(first, second), (step_iff_rootReducts free aligned unconditional rfl).mpr
        ⟨sourceState, targetState, member⟩⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨_, _⟩, step⟩, rfl, rfl⟩
      obtain ⟨sourceState, targetState, member⟩ := (step_iff_rootReducts free aligned unconditional rfl).mp step
      exact ⟨⟨⟨⟨_, _⟩, member⟩, sourceState, targetState⟩, rfl, rfl⟩

/-- **A μ-calculus formula about the runs of a first-order language holds exactly where its generated formula does**,
with the truth sets of the atoms' formulas as its environment. -/
theorem satisfies_runs_iff_sat (free : language.isEquationFree = true) (aligned : ReferenceProfile language)
    (unconditional : Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction.isUnconditionalAligned language = true)
    {atomCount : ℕ} (formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal atomCount)
    (consistent : muConsistent (fun _ => true) true formula = true) (atomFormulas : Fin atomCount → Formula 0)
    (term : Pattern) :
    satisfies (transitionSystem (Mettapedia.OSLF.Framework.BackwardSearch.between
        (Mettapedia.OSLF.Framework.HerbrandBridge.languageSpan language)
        Mettapedia.OSLF.Framework.FiniteModels.ObjectState))
      (fun index => {other | (referenceStructure relEnv language).sat Env.closed (atomFormulas index) other}) formula term ↔
      (referenceStructure relEnv language).sat Env.closed ((ofMu traversal true formula).subst atomFormulas) term := by
  rw [(referenceStructure relEnv language).sat_close]
  rw [satisfies_congr (lts' := transitionSystem (HigherOrder.stepSpan (referenceStructure relEnv language)))
    (ρ' := fun index => {other | (referenceStructure relEnv language).sat Env.closed (atomFormulas index) other})
    (runs_transitions_agree free aligned unconditional) (fun _ _ => Iff.rfl) formula term]
  exact (sat_ofMu (realizes_transitionSystem _) formula consistent (fun _ _ => Iff.rfl) term).symm

/-! ## Queries -/

variable (relEnv language type)

/-- **A query for the explored graph**: a μ-calculus formula over traversals with atoms, a generated formula for each
atom, and an abstraction with its explorer budget. -/
structure Query where
  atomCount : ℕ
  formula : Mettapedia.Logic.ModalMuCalculus.Formula Traversal atomCount
  atomFormulas : Fin atomCount → Formula 0
  normal : Pattern → Pattern
  same : Setoid Pattern
  atoms : Atoms same atomCount
  work : ℕ
  budget : ℕ

/-- **The generated formula of a query**: the embedding of its formula, with each atom's formula in place. -/
def Query.native (query : Query) : Formula 0 := (ofMu traversal true query.formula).subst query.atomFormulas

/-- **What makes a query sound**: a root-profile language with aligned rules, an abstraction meeting the explorer's
conditions on the well-sorted states, positive fixed points, and atoms that hold exactly where their formulas do. -/
structure Query.Valid (query : Query) : Prop where
  root : RootProfile language type
  aligned : ReferenceProfile language
  checked : Mettapedia.OSLF.MeTTaIL.Complete.Predecessors.equationsChecked (rootPlan language) = true
  abstraction : Abstraction (rootPlan language) [] type query.normal query.same (Sorted language type)
  consistent : muConsistent (fun _ => true) true query.formula = true
  atomsAgree : ∀ index state,
    query.atoms.holds index state = true ↔ (referenceStructure relEnv language).sat Env.closed (query.atomFormulas index) state

/-- Whether a term is well-sorted for the compiled root plan. -/
def sortedCheck (term : Pattern) : Bool :=
  checkOpenPatternWellSorted (rootPlan language).snapshot.language (rootPlan language).snapshot.free [] type term

/-- The verdict of the explored graph on a query at a term, as a Boolean answer. -/
def answerOf (query : Query) (term : Pattern) : Option Bool :=
  match verdict (rootPlan language) [] type query.normal term query.work query.formula query.atoms query.budget with
  | .proved => some true
  | .refuted => some false
  | .unknown _ => none

/-- **The decision**: the first query whose generated formula is the formula, at a well-sorted term. -/
def decides (queries : List Query) (formula : Formula 0) (term : Pattern) : Option Bool :=
  queries.findSome? fun query =>
    if decide (query.native = formula) && sortedCheck language type term then answerOf language type query term else none

variable {relEnv language type}

theorem verdict_future {query : Query} {term : Pattern} {answer : Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled.Verdict}
    (decisive : ∀ reason, answer ≠ .unknown reason)
    (read : verdict (rootPlan language) [] type query.normal term query.work query.formula query.atoms query.budget = answer) :
    FutureOnly query.formula = true ∧ fixedPointsPositive query.formula = true := by
  unfold verdict at read
  split_ifs at read with future positive
  · exact ⟨future, positive⟩
  · exact absurd read.symm (decisive _)
  · exact absurd read.symm (decisive _)
  · exact absurd read.symm (decisive _)

/-- **A valid query's explored verdict is exact** at a well-sorted term, about its generated formula. -/
theorem native_iff_satisfies {query : Query} (valid : query.Valid relEnv language type) {term : Pattern}
    (sorted : Sorted language type term) (future : FutureOnly query.formula = true)
    (positive : fixedPointsPositive query.formula = true) :
    (referenceStructure relEnv language).sat Env.closed query.native term ↔
      satisfies (transitionSystem (gsltSpan (theory (rootPlan language) [] type))) query.atoms.meaning query.formula term := by
  have envSame : (fun index => {other | (referenceStructure relEnv language).sat Env.closed (query.atomFormulas index) other}) =
      query.atoms.meaning := by
    funext index
    ext state
    exact (valid.atomsAgree index state).symm
  unfold Query.native
  rw [(referenceStructure relEnv language).sat_close, envSame]
  refine (sat_ofMu (realizes_transitionSystem _) query.formula valid.consistent
    (valuation := query.atoms.meaning) (fun _ _ => Iff.rfl) term).trans ?_
  exact (satisfies_transfer (first := gsltSpan (theory (rootPlan language) [] type))
    (second := HigherOrder.stepSpan (referenceStructure relEnv language)) (Sorted language type)
    (sorted_closed valid.root) (reference_sorted_closed valid.root valid.aligned)
    (fun _ _ sourceSorted targetSorted => plan_steps_agree valid.root valid.aligned sourceSorted targetSorted)
    query.formula future positive query.atoms.meaning sorted).symm

/-- **The explored verdicts of valid queries are exact.** -/
theorem decides_exact {queries : List Query} (valid : ∀ query ∈ queries, query.Valid relEnv language type)
    {formula : Formula 0} {term : Pattern} {answer : Bool} (decided : decides language type queries formula term = some answer) :
    (referenceStructure relEnv language).sat Env.closed formula term ↔ answer = true := by
  obtain ⟨query, member, found⟩ := List.exists_of_findSome?_eq_some decided
  by_cases matched : (decide (query.native = formula) && sortedCheck language type term) = true
  · rw [if_pos matched] at found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at matched
    obtain ⟨same, sortedChecked⟩ := matched
    have sorted : Sorted language type term := (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mp sortedChecked
    subst same
    have queryValid := valid query member
    unfold answerOf at found
    split at found
    · rename_i read
      cases found
      obtain ⟨future, positive⟩ := verdict_future (fun _ impossible => by cases impossible) read
      exact ⟨fun _ => rfl, fun _ => (native_iff_satisfies queryValid sorted future positive).mpr
        (verdict_proved queryValid.checked queryValid.abstraction sorted read)⟩
    · rename_i read
      cases found
      obtain ⟨future, positive⟩ := verdict_future (fun _ impossible => by cases impossible) read
      exact ⟨fun holds => absurd ((native_iff_satisfies queryValid sorted future positive).mp holds)
        (verdict_refuted queryValid.checked queryValid.abstraction sorted read), fun impossible => by cases impossible⟩
    · cases found
  · rw [if_neg matched] at found
    cases found

/-- **The explored graphs of valid queries, as a certified decider** of the language. -/
def decider (queries : List Query) (valid : ∀ query ∈ queries, query.Valid relEnv language type) :
    Decider relEnv language where
  decide := decides language type queries
  exact := decides_exact valid

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredDecider
