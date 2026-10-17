import Mettapedia.Logic.HostingStyles.AmbientSpace.Tokens
import Mettapedia.Logic.HostingStyles.AmbientSpace.Contexts

/-!
# Beside the candidate with a run: a member is the run at one space

The candidate with a run carries a space in a term; a member of the family
has its space outside.  Placing an atom in a run of the space of the member
compares the two (`runOfAtom`).

* **On patterns the two step relations are one.**  A step of the member at a
  space, from a pattern, is a step of the candidate with a run between the
  runs at that space (`run_of_ambient_stepAt`); and a step of the candidate
  from the run of a pattern without a run is the run of a step of the member
  (`ambient_of_run_stepAt`).  The root step of the member is the root step of
  the run; a congruence of the member is the congruence beneath the run that
  hands the space down; a step by beta or by release is found through the
  congruence of the subject of a run.
* **On terms the member at a space is hosted by the candidate with a run**
  (`placeInRun_hosting`): every closed atom of the member, placed in a run of
  the space, is a term of the candidate; no two atoms get one image; a step
  of the member is a step of the image; and a step of the image is the image
  of a step.  The last clause uses that a member never builds a run
  (`ambient_stepAt_tokens`): the reduct of the run of an atom of the member is
  the run of an atom of the member.
* **With contexts the comparison goes the other way.**  The image of every
  atom has exactly one run (`tokens_run_runOfAtom`), and a member has the
  application of an atom to an atom as a context.  So no map of theories from
  a reading of the member into a reading of the candidate with a run that
  places each closed atom in a run of the space is hosting
  (`placeInRun_not_hosting_with_contexts`): the image of the application
  context can use one of its two holes at most.  The member has that context
  with its two holes; the candidate with a run cannot receive it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## The two presentations differ by the run constructor -/

/-- The constructors of the ambient presentation are constructors of the
candidate with a run. -/
theorem ambient_terms_subset : ∀ rule ∈ ambient.terms, rule ∈ atomsReduce.terms := by decide

/-- Every constructor of the candidate with a run other than the run is a
constructor of the ambient presentation. -/
theorem atomsReduce_terms_kept :
    ∀ rule ∈ atomsReduce.terms, runLabel rule.label = false → rule ∈ ambient.terms := by
  decide

theorem atomsReduce_plain : ∀ rule ∈ atomsReduce.terms, usesBareCollection? rule = false := by
  decide

theorem ambient_no_run : ∀ rule ∈ ambient.terms, runLabel rule.label = false := by decide

theorem atomsReduce_run_params :
    ∀ rule ∈ atomsReduce.terms, rule.label = "prime-run" →
      rule.params = [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")] := by
  decide

/-- **A term of the ambient presentation has no run.** -/
theorem tokens_run_ambient {interface : Contexts.Interface}
    (term : Contexts.Term ambient interface) : tokens runLabel term.1 = 0 :=
  tokens_eq_zero_of_hasType ambient_no_run term.2.1 term.2.2.2.1

/-- A term of the ambient presentation, as a term of the candidate with a
run. -/
def inRunCandidate {interface : Contexts.Interface} (term : Contexts.Term ambient interface) :
    Contexts.Term atomsReduce interface :=
  ⟨term.1, wellSorted_of_terms_subset ambient_terms_subset term.2⟩

/-- A term of the candidate with a run that has no run, as a term of the
ambient presentation. -/
def ofRunFree {interface : Contexts.Interface} (term : Contexts.Term atomsReduce interface)
    (clean : tokens runLabel term.1 = 0) : Contexts.Term ambient interface :=
  ⟨term.1, wellSorted_of_tokens_eq_zero atomsReduce_terms_kept atomsReduce_plain term.2 clean⟩

/-- **An atom of the member at a space, placed in a run of that space**: a
closed atom of the candidate with a run. -/
def runOfAtom (space : SpaceTerm) (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    Contexts.Term atomsReduce AtomsReduce.closedAtom :=
  ⟨runPattern space.1 atom.1,
    wellSorted_apply_two (lang := atomsReduce) (label := "prime-run") (firstName := "space")
      (secondName := "subject") (by decide)
      (wellSorted_of_terms_subset ambient_terms_subset space.2)
      (wellSorted_of_terms_subset ambient_terms_subset atom.2)⟩

/-- **The image of an atom has exactly one run.** -/
theorem tokens_run_runOfAtom (space : SpaceTerm)
    (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    tokens runLabel (runOfAtom space atom).1 = 1 := by
  show tokens runLabel (runPattern space.1 atom.1) = 1
  simp [runPattern, tokens, tokensList, tokens_run_ambient space, tokens_run_ambient atom, runLabel]

/-- **Negative**: an atom of the member, as it is, has none. -/
theorem tokens_run_inRunCandidate (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    tokens runLabel (inRunCandidate atom).1 = 0 :=
  tokens_run_ambient atom

/-! ## On patterns: a step of the member is a step of the run -/

/-- **A step of the member at a space is a step of the candidate with a run
between the runs at that space.** -/
theorem run_of_ambient_stepAt {space : Pattern} :
    ∀ (fuel : Nat) {subject next : Pattern},
      StepAt (ambientEvaluator space) ambient fuel subject next →
        Step matchingEvaluator atomsReduce (runPattern space subject) (runPattern space next) := by
  intro fuel
  induction fuel with
  | zero => intro subject next step; cases step
  | succ fuel ih =>
      intro subject next step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [ambient_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [atomsReduce_rewrites]) space
          (step_beta (by simp [atomsReduce_rewrites]) domain body argument binder)⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppFunction (by simp [atomsReduce_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runAppArgument (by simp [atomsReduce_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiDomain (by simp [atomsReduce_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runPiBody (by simp [atomsReduce_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamDomain (by simp [atomsReduce_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨count, lifted⟩ := ih inner
        exact ⟨count + 1, step_runLamBody (by simp [atomsReduce_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨2, step_runSubject (by simp [atomsReduce_rewrites]) space
          (step_release (by simp [atomsReduce_rewrites]) atom)⟩
      · obtain ⟨answer, found, applied⟩ := root_inv matched premises
        rw [applied]
        exact ⟨1, step_runRoot (by simp [atomsReduce_rewrites]) found⟩

/-! ## On patterns: a step of the run of a pattern without a run -/

/-- An application of the run constructor matches no pattern without a
run. -/
theorem runFree_not_matched {parameters : List Pattern} {subject : Pattern} {bindings : Bindings}
    (clean : tokens runLabel subject = 0) :
    bindings ∉ matchPattern (.apply "prime-run" parameters) subject := by
  intro matched
  obtain ⟨arguments, rfl, -⟩ := eq_apply_of_matched matched
  exact absurd (tokens_apply_eq_zero_iff.mp clean).1 (by decide)

/-- **A step of the candidate with a run, from a pattern without a run, is a
step of the ambient presentation**, under every evaluator: it is a step by
beta, by a congruence of application, product or abstraction, or by
release. -/
theorem ambient_of_plain_stepAt {base other : BasePremiseEvaluator} :
    ∀ (fuel : Nat) {subject next : Pattern}, tokens runLabel subject = 0 →
      StepAt base atomsReduce fuel subject next → Step other ambient subject next := by
  intro fuel
  induction fuel with
  | zero => intro subject next _ step; cases step
  | succ fuel ih =>
      intro subject next clean step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
        rw [applied]
        exact ⟨1, step_beta (by simp [ambient_rewrites]) domain body argument binder⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appFunction_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts function (by simp)) inner
        exact ⟨count + 1, step_appFunction (by simp [ambient_rewrites]) argument lifted⟩
      · obtain ⟨function, argument, moved, rfl, inner, applied⟩ := appArgument_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts argument (by simp)) inner
        exact ⟨count + 1, step_appArgument (by simp [ambient_rewrites]) function lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piDomain_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts domain (by simp)) inner
        exact ⟨count + 1, step_piDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := piBody_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨count, lifted⟩ := ih cleanBody inner
        exact ⟨count + 1, step_piBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamDomain_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨count, lifted⟩ := ih (parts domain (by simp)) inner
        exact ⟨count + 1, step_lamDomain (by simp [ambient_rewrites]) body binder lifted⟩
      · obtain ⟨domain, binder, body, moved, rfl, inner, applied⟩ := lamBody_inv matched premises
        rw [applied]
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨count, lifted⟩ := ih cleanBody inner
        exact ⟨count + 1, step_lamBody (by simp [ambient_rewrites]) domain binder lifted⟩
      · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
        rw [applied]
        exact ⟨1, step_release (by simp [ambient_rewrites]) atom⟩
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)
      · exact absurd matched (runFree_not_matched clean)

/-- **A step of the candidate with a run, from the run of a pattern without a
run, is the run of a step of the member at the space of the run.** -/
theorem ambient_of_run_stepAt {space : Pattern} :
    ∀ (fuel : Nat) {subject target : Pattern}, tokens runLabel subject = 0 →
      StepAt matchingEvaluator atomsReduce fuel (runPattern space subject) target →
        ∃ next, target = runPattern space next ∧
          Step (ambientEvaluator space) ambient subject next := by
  intro fuel
  induction fuel with
  | zero => intro subject target _ step; cases step
  | succ fuel ih =>
      intro subject target clean step
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "App") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Pi") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "Lam") (by decide))
      · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
      · obtain ⟨otherSpace, inner, moved, shape, innerStep, applied⟩ :=
          runSubject_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨moved, applied, ambient_of_plain_stepAt fuel clean innerStep⟩
      · obtain ⟨otherSpace, inner, answer, shape, found, applied⟩ := runRoot_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        exact ⟨answer, applied, ⟨1, step_root (by simp [ambient_rewrites]) found⟩⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppFunction_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih (parts function (by simp)) inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_appFunction (by simp [ambient_rewrites]) argument
          lifted⟩⟩
      · obtain ⟨otherSpace, function, argument, moved, shape, inner, applied⟩ :=
          runAppArgument_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih (parts argument (by simp)) inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_appArgument (by simp [ambient_rewrites]) function
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih (parts domain (by simp)) inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_piDomain (by simp [ambient_rewrites]) body binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runPiBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih cleanBody inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_piBody (by simp [ambient_rewrites]) domain binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamDomain_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih (parts domain (by simp)) inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_lamDomain (by simp [ambient_rewrites]) body binder
          lifted⟩⟩
      · obtain ⟨otherSpace, domain, binder, body, moved, shape, inner, applied⟩ :=
          runLamBody_inv matched premises
        obtain ⟨rfl, rfl⟩ := runPattern_injective shape
        obtain ⟨-, parts⟩ := tokens_apply_eq_zero_iff.mp clean
        have cleanBody : tokens runLabel body = 0 := by
          have abstraction := parts (.lambda binder body) (by simp)
          rwa [tokens] at abstraction
        obtain ⟨reached, same, ⟨count, lifted⟩⟩ := ih cleanBody inner
        obtain ⟨-, rfl⟩ := runPattern_injective same
        exact ⟨_, applied, ⟨count + 1, step_lamBody (by simp [ambient_rewrites]) domain binder
          lifted⟩⟩

/-- **On patterns without a run, the steps of the run at a space are the runs
of the steps of the member at that space.** -/
theorem run_step_iff_ambient {space subject target : Pattern}
    (clean : tokens runLabel subject = 0) :
    Step matchingEvaluator atomsReduce (runPattern space subject) target ↔
      ∃ next, target = runPattern space next ∧
        Step (ambientEvaluator space) ambient subject next := by
  constructor
  · rintro ⟨fuel, step⟩
    exact ambient_of_run_stepAt fuel clean step
  · rintro ⟨next, rfl, ⟨fuel, step⟩⟩
    exact run_of_ambient_stepAt fuel step

/-! ## On terms -/

/-- A term of the candidate with a run whose contraction is a run is a run of
patterns with those contractions. -/
theorem eq_run_of_contract {stage : List TypeExpr}
    (term : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) {space subject : Pattern}
    (same : contract term.1 = runPattern space subject) :
    ∃ otherSpace otherSubject, term.1 = runPattern otherSpace otherSubject ∧
      contract otherSpace = space ∧ contract otherSubject = subject := by
  obtain ⟨pattern, sorted⟩ := term
  cases pattern with
  | bvar index => simp [contract, runPattern] at same
  | fvar name => simp [contract, runPattern] at same
  | apply label arguments =>
      have notQuote : label ≠ "prime-quote" := by
        intro isQuote
        obtain ⟨rule, member, sameLabel, type⟩ := declared_constructor_of_hasType_apply sorted.1
        have category :=
          (atomsReduce_quoteDropSorted.quote rule member (sameLabel.trans isQuote)).1
        rw [category] at type
        exact absurd (TypeExpr.base.inj type) (by decide)
      have unfolded : contract (Pattern.apply label arguments) = runPattern space subject := same
      rw [contract_apply_of_ne notQuote] at unfolded
      simp only [runPattern, Pattern.apply.injEq] at unfolded
      obtain ⟨rfl, parts⟩ := unfolded
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, more⟩⟩⟩
      · simp at parts
      · simp at parts
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at parts
        exact ⟨first, second, rfl, parts.1, parts.2⟩
      · simp at parts
  | lambda binder body => simp [contract, runPattern] at same
  | multiLambda arity binders body => simp [contract, runPattern] at same
  | subst body replacement => simp [contract, runPattern] at same
  | collection kind elements rest => simp [contract, runPattern] at same

/-- The space and the subject of a run that is a term are terms. -/
theorem run_parts_wellSorted {space subject : Pattern} {bound : List TypeExpr}
    (sorted : OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom")
      (runPattern space subject)) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Space") space ∧
      OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom") subject := by
  obtain ⟨typed, canonical, object, scope⟩ := sorted
  obtain ⟨rule, member, label, arguments⟩ := hasType_apply_inv typed
  rw [atomsReduce_run_params rule member label] at arguments
  obtain ⟨spaceTyped, rest⟩ := arguments.simple_cons_inv
  obtain ⟨subjectTyped, -⟩ := rest.simple_cons_inv
  have canonicalParts : space.hasCanonicalBinderMetadata = true ∧
      subject.hasCanonicalBinderMetadata = true := by
    simpa [runPattern, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  have objectParts : isObjectPattern space = true ∧ isObjectPattern subject = true := by
    simpa [runPattern, isObjectPattern, isObjectPatternList] using object
  have scopeParts : space.isWellScopedAt bound.length = true ∧
      subject.isWellScopedAt bound.length = true := by
    have whole : (runPattern space subject).isWellScopedAt bound.length = true := scope
    simpa [runPattern, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using whole
  exact ⟨⟨spaceTyped, canonicalParts.1, objectParts.1, scopeParts.1⟩,
    ⟨subjectTyped, canonicalParts.2, objectParts.2, scopeParts.2⟩⟩

theorem contract_runOfAtom (space : SpaceTerm)
    (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    contract (runOfAtom space atom).1 = runPattern (contract space.1) (contract atom.1) :=
  contract_runPattern' space.1 atom.1

/-- Atoms that the member identifies have runs that the candidate with a run
identifies, and conversely. -/
theorem runOfAtom_related_iff {base other : BasePremiseEvaluator} (space : SpaceTerm)
    {first second : Contexts.Term ambient AtomsReduce.closedAtom} :
    (termSetoid base atomsReduce AtomsReduce.closedAtom).r (runOfAtom space first)
        (runOfAtom space second) ↔
      (termSetoid other ambient AtomsReduce.closedAtom).r first second := by
  rw [atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted,
    ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted, contract_runOfAtom,
    contract_runOfAtom]
  constructor
  · intro same
    exact (runPattern_injective same).2
  · intro same
    rw [same]

/-- **The member at a space, in the candidate with a run**: a closed atom is
placed in a run of the space. -/
def placeInRun (space : SpaceTerm) :
    ContextMap ((ambientTheory space).gslt AtomsReduce.closedAtom).termsAlone atomsReduceTheory :=
  ContextMap.ofTerms (source := (ambientTheory space).gslt AtomsReduce.closedAtom)
    (target := atomsReduceTheory) AtomsReduce.closedAtom (fun atom => runOfAtom space atom)
    (fun {_ _} related => (runOfAtom_related_iff space).mpr related)

/-- **On terms, the member at a space is hosted by the candidate with a run,
by placing each atom in a run of that space**: no two atoms get one image, a
step of the member is a step of the image, and a step of the image is the
image of a step. -/
theorem placeInRun_hosting (space : SpaceTerm) : (placeInRun space).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff
    (source := (ambientTheory space).gslt AtomsReduce.closedAtom) (target := atomsReduceTheory)
    AtomsReduce.closedAtom (fun atom => runOfAtom space atom)
    (fun {_ _} related => (runOfAtom_related_iff space).mpr related)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    exact (runOfAtom_related_iff space).mp related
  · rintro first next ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩
    exact ⟨runOfAtom space redex, runOfAtom space contractum,
      (runOfAtom_related_iff space).mpr before, run_of_ambient_stepAt fuel fired,
      (runOfAtom_related_iff space).mpr after⟩
  · rintro first target ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩
    have sameContract : contract redex.1 = runPattern (contract space.1) (contract first.1) :=
      ((atomsReduce_quoteDropOnly.contract_eq before).symm).trans (contract_runOfAtom space first)
    obtain ⟨otherSpace, subject, redexShape, spaceSame, subjectSame⟩ :=
      eq_run_of_contract redex sameContract
    have cleanSubject : tokens runLabel subject = 0 := by
      rw [← tokens_contract (by decide) (by decide) subject, subjectSame,
        tokens_contract (by decide) (by decide)]
      exact tokens_run_ambient first
    rw [redexShape] at fired
    obtain ⟨reached, contractumShape, moved⟩ := ambient_of_run_stepAt fuel cleanSubject fired
    have sameEvaluator : ambientEvaluator otherSpace = ambientEvaluator space.1 :=
      ambientEvaluator_congr spaceSame
    rw [sameEvaluator] at moved
    obtain ⟨count, movedAt⟩ := moved
    have cleanSpace : tokens runLabel (contract space.1) = 0 := by
      rw [tokens_contract (by decide) (by decide)]
      exact tokens_run_ambient space
    have cleanReached : tokens runLabel reached = 0 :=
      ambient_stepAt_tokens (by decide) (by decide) cleanSpace count movedAt cleanSubject
    have redexParts := run_parts_wellSorted (redexShape ▸ redex.2)
    have contractumParts := run_parts_wellSorted (contractumShape ▸ contractum.2)
    let subjectTerm : Contexts.Term ambient AtomsReduce.closedAtom :=
      ofRunFree ⟨subject, redexParts.2⟩ cleanSubject
    let reachedTerm : Contexts.Term ambient AtomsReduce.closedAtom :=
      ofRunFree ⟨reached, contractumParts.2⟩ cleanReached
    refine ⟨reachedTerm, ⟨subjectTerm, reachedTerm, ?_, ⟨count, movedAt⟩,
      Relation.EqvGen.refl _⟩, ?_⟩
    · exact (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr subjectSame.symm
    · refine (atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted).mpr ?_
      rw [← atomsReduce_quoteDropOnly.contract_eq after, contractumShape, contract_runOfAtom,
        contract_runPattern', spaceSame]
      rfl

/-- The sentence: the member at a space is hosted, on its closed atoms, by
the candidate with a run. -/
theorem member_hostedBy_atomsReduce (space : SpaceTerm) :
    HostedBy ((ambientTheory space).gslt AtomsReduce.closedAtom).termsAlone atomsReduceTheory :=
  ⟨placeInRun space, placeInRun_hosting space⟩

/-! ## With contexts -/

/-- The application of a closed atom of the member to a closed atom, as a
context of each of its readings. -/
def memberApplication (space : SpaceTerm) (regions : Contexts.Interface → Prop) :
    ((ambientTheory space).regionReading regions).Context
      (fun _ : Bool => AtomsReduce.closedAtom) AtomsReduce.closedAtom :=
  ContextTheory.RegionContext.ofContext (theory := ambientTheory space) (declared := regions)
    (applicationContextOf ambientPresentation ambient_carriesAtoms []) fun free _ => free

/-- **With contexts, no map of theories that places each closed atom of a
member in a run of its space is hosting**, from any reading of the member and
into any reading of the candidate with a run.  The member has the application
of an atom to an atom as a context of two holes; each image has one run, so
the image of that context can use one of its holes at most. -/
theorem placeInRun_not_hosting_with_contexts (space : SpaceTerm)
    {regions targetRegions : Contexts.Interface → Prop}
    (map : ContextMap ((ambientTheory space).regionReading regions)
      (atomsReduceTheory.regionReading targetRegions))
    (places : ∀ atom : Contexts.Term ambient AtomsReduce.closedAtom,
      (map.term (origin := AtomsReduce.closedAtom) atom).1 = (runOfAtom space atom).1) :
    ¬ map.Hosting :=
  not_hosting_of_uniform_tokens atomsReduce_quoteDropOnly (counted := runLabel) (by decide)
    (by decide) map (memberApplication space regions) Nat.one_pos
    (fun atom => (congrArg (tokens runLabel) (places atom)).trans (tokens_run_runOfAtom space atom))
    (fixed := atomTerm 0 (.srt .type)) (still := atomTerm 0 (.srt .type))
    (other := atomTerm 0 (.srt .kind))
    (fun related => by
      have same := ambient_quoteDropOnly.contract_eq related
      have closed : contract (.apply "App" [symbolAtom 0, symbolAtom 0]) =
          contract (.apply "App" [symbolAtom 0, symbolAtom 1]) := same
      revert closed
      decide)
    (fun related => by
      have same := ambient_quoteDropOnly.contract_eq related
      have closed : contract (.apply "App" [symbolAtom 0, symbolAtom 0]) =
          contract (.apply "App" [symbolAtom 1, symbolAtom 0]) := same
      revert closed
      decide)

#print axioms tokens_run_ambient
#print axioms tokens_run_runOfAtom
#print axioms run_of_ambient_stepAt
#print axioms ambient_of_plain_stepAt
#print axioms ambient_of_run_stepAt
#print axioms run_step_iff_ambient
#print axioms eq_run_of_contract
#print axioms runOfAtom_related_iff
#print axioms placeInRun_hosting
#print axioms member_hostedBy_atomsReduce
#print axioms placeInRun_not_hosting_with_contexts

end Mettapedia.Logic.HostingStyles.AmbientSpace
