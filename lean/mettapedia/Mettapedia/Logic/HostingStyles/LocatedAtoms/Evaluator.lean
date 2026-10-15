import Mettapedia.Logic.HostingStyles.LocatedAtoms.NormalForm

/-!
# An evaluator that reads located atoms up to their static equivalence

The matching evaluator reads the space and the subject of a run up to the
equation of quotation and dropping.  Under the equations of a run this is no
longer reading up to the static equivalence: the run of an application and
the application of the runs are one term, and the matching evaluator answers
them differently (`matchingEvaluator_not_respectsStatics`).

This module gives the evaluator that reads through the normal form.

* The normal form of a run says where each leaf of its subject is located.
  `located?` recognizes a normal form all of whose leaves are located in one
  space: it returns that space and the atom without its runs (`unlocate`).
  The normal form of the run of an atom without a run, in a space, is
  recognized as that space and that atom (`located?_push`); a pattern is
  recognized only as what it is (`located?_sound`).
* `locatedAnswers space subject` are the answers of the space **in which the
  subject is located**, for the atom without its runs, each answer located in
  that space.  If the subject is already located in an inner space, the outer
  space is not read; if its leaves are in two spaces, there is no answer.
* `locatedEvaluator` answers the premise of the root step of a run by them.
  **It respects the static equivalence** (`locatedEvaluator_respectsStatics`),
  because it reads its two arguments through the normal form only.  So the
  presentation under it is a presented candidate (`locatedProbe`).
* At a space and a subject that are their own normal forms and have no run,
  the answers are those of the matching evaluator, each in a run
  (`locatedAnswers_of_plain`).

The root step of a run under this evaluator is read on patterns in
`step_locatedRoot` and `locatedRoot_inv`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars_zero)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace (tokens_apply_eq_zero_iff tokens_eq_zero_of_mem)

/-! ## An atom without its runs -/

/-- Remove a run at the root of a node. -/
def unlocateRoot (label : String) (arguments : List Pattern) : Pattern :=
  if label = "prime-run" then
    match arguments with
    | [_, subject] => subject
    | _ => .apply label arguments
  else .apply label arguments

mutual
  /-- **A pattern without its runs**: every run is replaced by its subject. -/
  def unlocate : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments => unlocateRoot label (unlocateList arguments)
    | .lambda binder body => .lambda binder (unlocate body)
    | .multiLambda arity binders body => .multiLambda arity binders (unlocate body)
    | .subst body replacement => .subst (unlocate body) (unlocate replacement)
    | .collection kind elements rest => .collection kind (unlocateList elements) rest

  /-- Removing runs, along a list. -/
  def unlocateList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => unlocate pattern :: unlocateList patterns
end

@[simp] theorem unlocateList_eq_map :
    ∀ patterns : List Pattern, unlocateList patterns = patterns.map unlocate
  | [] => rfl
  | pattern :: patterns => by
      simp only [unlocateList, List.map_cons, unlocateList_eq_map patterns]

theorem unlocate_apply (label : String) (arguments : List Pattern) :
    unlocate (.apply label arguments) = unlocateRoot label (arguments.map unlocate) := by
  rw [unlocate, unlocateList_eq_map]

/-- **Positive**: a run is replaced by its subject. -/
theorem unlocate_runPattern (space subject : Pattern) :
    unlocate (runPattern space subject) = unlocate subject := by
  simp [runPattern, unlocate_apply, unlocateRoot]

theorem unlocate_apply_of_ne {label : String} (noRun : label ≠ "prime-run")
    (arguments : List Pattern) :
    unlocate (.apply label arguments) = .apply label (arguments.map unlocate) := by
  rw [unlocate_apply]
  unfold unlocateRoot
  rw [if_neg noRun]

/-- **Negative**: a pattern without a run is unchanged. -/
theorem unlocate_of_clean (pattern : Pattern) :
    tokens runLabel pattern = 0 → unlocate pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [unlocate]
  | hfvar name => intro _; rw [unlocate]
  | happly label arguments ih =>
      intro clean
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp clean
      have noRun : label ≠ "prime-run" := by simpa [runLabel] using uncounted
      rw [unlocate_apply_of_ne noRun]
      congr 1
      exact (List.map_congr_left (g := id) fun argument member =>
        ih argument member (each argument member)).trans (List.map_id arguments)
  | hlambda binder body ih => intro clean; rw [unlocate, ih (by rwa [tokens] at clean)]
  | hmultiLambda arity binders body ih =>
      intro clean
      rw [unlocate, ih (by rwa [tokens] at clean)]
  | hsubst body replacement ihBody ihReplacement =>
      intro clean
      rw [tokens] at clean
      rw [unlocate, ihBody (by omega), ihReplacement (by omega)]
  | hcollection kind elements rest ih =>
      intro clean
      have each := tokens_eq_zero_of_mem (counted := runLabel) (by rwa [tokens] at clean)
      rw [unlocate, unlocateList_eq_map]
      congr 1
      exact (List.map_congr_left (g := id) fun element member =>
        ih element member (each element member)).trans (List.map_id elements)

/-- **The atom without its runs, of an atom without a run pushed in a space,
is the atom.** -/
theorem unlocate_push (space : Pattern) (pattern : Pattern) :
    tokens runLabel pattern = 0 → unlocate (push space pattern) = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [push, unlocate_runPattern, unlocate]
  | hfvar name => intro _; rw [push, unlocate_runPattern, unlocate]
  | happly label arguments ih =>
      intro clean
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp clean
      have noRun : label ≠ "prime-run" := by simpa [runLabel] using uncounted
      rw [push_apply]
      unfold pushRoot
      split_ifs with spread isRun
      · rw [unlocate_apply_of_ne noRun, List.map_map]
        congr 1
        exact (List.map_congr_left (g := id) fun argument member =>
          ih argument member (each argument member)).trans (List.map_id arguments)
      · exact absurd isRun.1 noRun
      · rw [unlocate_runPattern]
        exact unlocate_of_clean _ clean
  | hlambda binder body ih => intro clean; rw [push, unlocate, ih (by rwa [tokens] at clean)]
  | hmultiLambda arity binders body _ =>
      intro clean
      rw [push, unlocate_runPattern]
      exact unlocate_of_clean _ clean
  | hsubst body replacement _ _ =>
      intro clean
      rw [push, unlocate_runPattern]
      exact unlocate_of_clean _ clean
  | hcollection kind elements rest _ =>
      intro clean
      rw [push, unlocate_runPattern]
      exact unlocate_of_clean _ clean

/-! ## The space of the first located leaf -/

mutual
  /-- **The space of the first run of a pattern**, read from the left and
  through the nodes that are no run. -/
  def headSpace? : Pattern → Option Pattern
    | .apply label arguments =>
        if label = "prime-run" then
          match arguments with
          | [space, _] => some space
          | _ => none
        else headSpaceList? arguments
    | .lambda _ body => headSpace? body
    | .bvar _ => none
    | .fvar _ => none
    | .multiLambda _ _ _ => none
    | .subst _ _ => none
    | .collection _ _ _ => none

  /-- The space of the first run of a list of patterns. -/
  def headSpaceList? : List Pattern → Option Pattern
    | [] => none
    | pattern :: patterns =>
        match headSpace? pattern with
        | some space => some space
        | none => headSpaceList? patterns
end

theorem headSpace?_runPattern (space subject : Pattern) :
    headSpace? (runPattern space subject) = some space := by
  simp [runPattern, headSpace?]

/-- **The first run of an atom without a run, pushed in a space, is in that
space.** -/
theorem headSpace?_push (space : Pattern) (pattern : Pattern) :
    tokens runLabel pattern = 0 → headSpace? (push space pattern) = some space := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [push, headSpace?_runPattern]
  | hfvar name => intro _; rw [push, headSpace?_runPattern]
  | happly label arguments ih =>
      intro clean
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp clean
      have noRun : label ≠ "prime-run" := by simpa [runLabel] using uncounted
      rw [push_apply]
      unfold pushRoot
      split_ifs with spread isRun
      · match arguments, spread, ih, each with
        | [first, second], _, ih, each =>
            have head := ih first (by simp) (each first (by simp))
            simp [headSpace?, noRun, headSpaceList?, head]
        | [], spread, _, _ => simp [distributes] at spread
        | [_], spread, _, _ => simp [distributes] at spread
        | _ :: _ :: _ :: _, spread, _, _ => simp [distributes] at spread
      · exact absurd isRun.1 noRun
      · exact headSpace?_runPattern space _
  | hlambda binder body ih => intro clean; rw [push, headSpace?, ih (by rwa [tokens] at clean)]
  | hmultiLambda arity binders body _ => intro _; rw [push, headSpace?_runPattern]
  | hsubst body replacement _ _ => intro _; rw [push, headSpace?_runPattern]
  | hcollection kind elements rest _ => intro _; rw [push, headSpace?_runPattern]

/-! ## Atoms located in one space -/

/-- **A pattern all of whose leaves are located in one space**, as that space
and the pattern without its runs: the space of its first run, if the pattern
is its pattern without runs pushed in that space. -/
def located? (pattern : Pattern) : Option (Pattern × Pattern) :=
  match headSpace? pattern with
  | some space =>
      if push space (unlocate pattern) = pattern then some (space, unlocate pattern) else none
  | none => none

/-- **Positive**: an atom without a run, pushed in a space, is located in
that space. -/
theorem located?_push {pattern : Pattern} (clean : tokens runLabel pattern = 0) (space : Pattern) :
    located? (push space pattern) = some (space, pattern) := by
  unfold located?
  rw [headSpace?_push space pattern clean, unlocate_push space pattern clean]
  simp

/-- **A pattern is recognized only as what it is.** -/
theorem located?_sound {pattern space plain : Pattern}
    (found : located? pattern = some (space, plain)) : pattern = push space plain := by
  unfold located? at found
  split at found
  · split_ifs at found with same
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact same.symm
  · cases found

/-- **Negative**: an atom without a run is located in no space. -/
theorem located?_unitAtom : located? unitAtom = none := by decide

/-! ## The evaluator -/

/-- **The answers for the subject of a run in a space**: if the leaves of the
normal form of the run are located in one space, the answers of that space
for the subject without its runs, each located in that space. -/
def locatedAnswers (space subject : Pattern) : List Pattern :=
  match located? (settle (runPattern space subject)) with
  | some (inner, plain) => (matchResults inner plain).map (runPattern inner)
  | none => []

/-- **The evaluator of located atoms.**  It answers the premise of the root
step of a run with the answers for its subject, and it answers no other
premise. -/
def locatedEvaluator : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "PrimeStep" [space, subject, .fvar answer] =>
      (locatedAnswers (applyBindings bindings space) (applyBindings bindings subject)).map
        fun result => (answer, result) :: bindings
  | _ => []

/-- The answers, from the normal form of the run. -/
theorem locatedAnswers_of_settle {space subject inner plain : Pattern}
    (normal : settle (runPattern space subject) = push inner plain)
    (clean : tokens runLabel plain = 0) :
    locatedAnswers space subject = (matchResults inner plain).map (runPattern inner) := by
  unfold locatedAnswers
  rw [normal, located?_push clean]

/-- **At a space and a subject that are their own normal forms, the subject
without a run, the answers are those of the space, each in a run.** -/
theorem locatedAnswers_of_plain {space subject : Pattern} (spaceNormal : settle space = space)
    (subjectNormal : settle subject = subject) (clean : tokens runLabel subject = 0) :
    locatedAnswers space subject = (matchResults space subject).map (runPattern space) :=
  locatedAnswers_of_settle (by rw [settle_runPattern, spaceNormal, subjectNormal]) clean

/-- The answers depend on the normal form of the run alone. -/
theorem locatedAnswers_congr {space subject otherSpace otherSubject : Pattern}
    (spaces : settle space = settle otherSpace) (subjects : settle subject = settle otherSubject) :
    locatedAnswers space subject = locatedAnswers otherSpace otherSubject := by
  unfold locatedAnswers
  rw [settle_runPattern, settle_runPattern, spaces, subjects]

/-- **The evaluator of located atoms respects the static equivalence.** -/
theorem locatedEvaluator_respectsStatics : RespectsStatics locatedEvaluator located := by
  intro premise member first second related result answered
  have settled : BindingsRelated (fun left right => settle left = settle right) first second :=
    related.mono fun _ _ equivalent => settle_eq_of_equiv equivalent
  rw [located_premises] at member
  rcases atomsReduce_premises premise member with listed | ⟨source, target, rfl⟩
  swap
  · simp [locatedEvaluator] at answered
  rw [presentedPremises_probeWithRun] at listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · simp [locatedEvaluator] at answered
  · simp [locatedEvaluator] at answered
  · simp [locatedEvaluator] at answered
  · have answers : result ∈ (locatedAnswers (applyBindings first (.fvar "space"))
        (applyBindings first (.fvar "subject"))).map fun answer => ("answer", answer) :: first :=
      answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [locatedAnswers_congr
      (BindingsRelated.lookup (relation := fun left right => settle left = settle right)
        (fun _ => rfl) settled "space")
      (BindingsRelated.lookup (relation := fun left right => settle left = settle right)
        (fun _ => rfl) settled "subject")] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (locatedAnswers (applyBindings second (.fvar "space"))
      (applyBindings second (.fvar "subject"))).map fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩

/-- **The candidate with located atoms, as a presented candidate**: the
presentation under the evaluator of located atoms. -/
def locatedProbe : PresentedCandidate where
  presentation := locatedPresentation
  evaluator := locatedEvaluator
  respects := locatedEvaluator_respectsStatics

/-- The theory of the candidate with located atoms, with all its contexts. -/
abbrev locatedTheory : ContextTheory.{0} := contextTheory locatedEvaluator locatedPresentation

theorem locatedProbe_theory : locatedProbe.theory = locatedTheory := rfl

/-! ## The matching evaluator does not respect the equations of a run -/

/-- A space that stores one rule, whose left side is an application of two
runs. -/
def spelledSpace : Pattern :=
  spaceOfAtoms [.apply "=" [applicationOfRuns.1, unitAtom]]

/-- **Negative**: the matching evaluator does not respect the static
equivalence of the candidate with located atoms.  A space stores a rule whose
left side is the application of two runs; the matching evaluator answers that
application, and it does not answer the run of the application, which is the
same term. -/
theorem matchingEvaluator_not_respectsStatics : ¬ RespectsStatics matchingEvaluator located := by
  intro respects
  have related : BindingsRelated (EquationEquiv matchingEvaluator located)
      [("subject", applicationOfRuns.1), ("space", spelledSpace)]
      [("subject", runOfApplication.1), ("space", spelledSpace)] :=
    .cons ⟨rfl, .symm _ _
      (equationInstance_equivalent (runApplication_instance emptySpace unitAtom unitAtom))⟩
      (.cons ⟨rfl, .refl _⟩ .nil)
  have listed : runPremise ∈ presentedPremises located := by
    rw [located_premises]
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨runRewrite, by simp [atomsReduce_rewrites], List.mem_singleton.mpr rfl⟩)
  have spaceFixed : contract spelledSpace = spelledSpace := by decide
  have firstFixed : contract applicationOfRuns.1 = applicationOfRuns.1 := by decide
  have secondFixed : contract runOfApplication.1 = runOfApplication.1 := by decide
  have answered : (("answer", unitAtom) :: [("subject", applicationOfRuns.1),
      ("space", spelledSpace)] : Bindings) ∈
      matchingEvaluator located [("subject", applicationOfRuns.1), ("space", spelledSpace)]
        runPremise := by
    show _ ∈ (matchResults
      (contract (applyBindings [("subject", applicationOfRuns.1), ("space", spelledSpace)]
        (.fvar "space")))
      (contract (applyBindings [("subject", applicationOfRuns.1), ("space", spelledSpace)]
        (.fvar "subject")))).map
        fun result => ("answer", result) ::
          [("subject", applicationOfRuns.1), ("space", spelledSpace)]
    have spaceValue : applyBindings [("subject", applicationOfRuns.1), ("space", spelledSpace)]
        (.fvar "space") = spelledSpace := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", applicationOfRuns.1), ("space", spelledSpace)]
        (.fvar "subject") = applicationOfRuns.1 := by simp [applyBindings]
    rw [spaceValue, subjectValue, spaceFixed, firstFixed]
    refine List.mem_map.mpr ⟨unitAtom, ?_, rfl⟩
    rw [spelledSpace, mem_matchResults_spaceOfAtoms]
    refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
    rw [atomResults_equation _ (by decide) (by decide)]
    simp [applicationOfRuns, runPattern, emptySpace, unitAtom, asRule, asRuleList, matchPattern,
      matchArgs, mergeBindings, applyBindings]
  obtain ⟨other, found, -⟩ := respects runPremise listed related _ answered
  have none : matchingEvaluator located [("subject", runOfApplication.1), ("space", spelledSpace)]
      runPremise = [] := by
    show (matchResults
      (contract (applyBindings [("subject", runOfApplication.1), ("space", spelledSpace)]
        (.fvar "space")))
      (contract (applyBindings [("subject", runOfApplication.1), ("space", spelledSpace)]
        (.fvar "subject")))).map
        (fun result => ("answer", result) ::
          [("subject", runOfApplication.1), ("space", spelledSpace)]) = []
    have spaceValue : applyBindings [("subject", runOfApplication.1), ("space", spelledSpace)]
        (.fvar "space") = spelledSpace := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", runOfApplication.1), ("space", spelledSpace)]
        (.fvar "subject") = runOfApplication.1 := by simp [applyBindings]
    rw [spaceValue, subjectValue, spaceFixed, secondFixed]
    have empty : matchResults spelledSpace runOfApplication.1 = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro answer member
      rw [spelledSpace, mem_matchResults_spaceOfAtoms] at member
      obtain ⟨atom, inAtoms, inResults⟩ := member
      rw [List.mem_singleton.mp inAtoms, atomResults_equation _ (by decide) (by decide)] at inResults
      simp [applicationOfRuns, runOfApplication, runPattern, emptySpace, unitAtom, asRule,
        asRuleList, matchPattern] at inResults
    rw [empty]
    rfl
  rw [none] at found
  cases found

/-! ## The root step of a run, on patterns -/

variable {lang : LanguageDef}

/-- **The root step of a run**, under the evaluator of located atoms: to the
run of an answer for its subject. -/
theorem step_locatedRoot (member : runRewrite ∈ lang.rewrites) {space subject answer : Pattern}
    (found : answer ∈ locatedAnswers space subject) :
    StepAt locatedEvaluator lang 1 (runPattern space subject) (runPattern space answer) := by
  refine stepAt_of_rule (rule := runRewrite) member
    (initial := [("subject", subject), ("space", space)])
    (final := [("answer", answer), ("subject", subject), ("space", space)]) ?_ ?_ ?_
  · simp [runRewrite, runPattern, matchPattern, matchArgs, mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (locatedAnswers
      (applyBindings [("subject", subject), ("space", space)] (.fvar "space"))
      (applyBindings [("subject", subject), ("space", space)] (.fvar "subject"))).map
        fun result => ("answer", result) :: [("subject", subject), ("space", space)]
    have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
        space := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
        subject := by simp [applyBindings]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [applyRuleBindings, runRewrite, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]

/-- What a root step of a run is, under the evaluator of located atoms. -/
theorem locatedRoot_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runRewrite.left source)
    (premises : PremisesAt locatedEvaluator lang fuel initial runRewrite.premises final) :
    ∃ space subject answer, source = runPattern space subject ∧
      answer ∈ locatedAnswers space subject ∧
        applyRuleBindings runRewrite final = runPattern space answer := by
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide)
    (show initial ∈ matchPattern (runPattern (.fvar "space") (.fvar "subject")) source from matched)
  have premises' : PremisesAt locatedEvaluator lang fuel [("subject", subject), ("space", space)]
      [runPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (locatedAnswers
              (applyBindings [("subject", subject), ("space", space)] (.fvar "space"))
              (applyBindings [("subject", subject), ("space", space)] (.fvar "subject"))).map
                fun result => ("answer", result) :: [("subject", subject), ("space", space)] :=
            answered
          have spaceValue : applyBindings [("subject", subject), ("space", space)]
              (.fvar "space") = space := by simp [applyBindings]
          have subjectValue : applyBindings [("subject", subject), ("space", space)]
              (.fvar "subject") = subject := by simp [applyBindings]
          rw [spaceValue, subjectValue] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          exact ⟨space, subject, answer, rfl, found, by
            simp [applyRuleBindings, runRewrite, runPattern, applyBindingsScoped, captureDepth,
              captureDepthList, liftBVars_zero]⟩

#print axioms unlocate_push
#print axioms headSpace?_push
#print axioms located?_push
#print axioms located?_sound
#print axioms locatedAnswers_of_plain
#print axioms locatedEvaluator_respectsStatics
#print axioms locatedProbe
#print axioms matchingEvaluator_not_respectsStatics
#print axioms step_locatedRoot
#print axioms locatedRoot_inv

end Mettapedia.Logic.HostingStyles.LocatedAtoms
