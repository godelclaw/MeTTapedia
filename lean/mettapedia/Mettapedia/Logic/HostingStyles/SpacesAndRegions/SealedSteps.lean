import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Sealed

/-!
# What a step of the candidate keeps

A step of the candidate is made of few operations: it takes an application,
an abstraction, a product or a run apart and puts it together again around a
step of a part; it instantiates the binder of an abstraction; it releases a
dropped quotation; and it replaces a pattern by an answer of a space for it.
`OperationInvariant holds space` says that a property of patterns, by the
number of binders around them, is kept by each of these operations, at the
spaces with the property `space`.

* **One induction over the thirty-three rewrites**
  (`OperationInvariant.stepAt`): such a property is kept by every step, in
  every language with the rewrites of `allHeaded`, under every guard, at
  every ambient space with the property of spaces.  The run is no special
  case: a run has the property exactly when its space has the property of
  spaces and its subject has the property.
* **Sealed with plain runs is such a property**, at the plain spaces
  (`sealedWithPlainRuns_invariant`).  The part of the answers: the values
  that a first-order left side binds are parts of the subject
  (`holds_of_matched`), a plain space stores closed atoms without quotation,
  and an instance of such an atom by sealed values is sealed
  (`sealedWithPlainRuns_of_mem_matchResults`).  The plain spaces are the
  spaces of the runs of a sealed pattern; the ambient spaces at which a step
  keeps a pattern sealed are a larger class, given in the module of the
  spaces that quote only what was quoted.
* **A hypothesis on the space is needed.**  A space is free to store a rule
  whose right side has its variable beneath a quotation; the evaluator reads
  the variable atoms of a stored atom as the variables of a rule, those
  beneath a quotation too.  At the space of the rule `$0 ⟶ *@$0` a sealed
  abstraction steps to one that is not sealed
  (`quotingSpace_unseals`), so sealing with every space is no such property
  (`sealing_not_invariant_at_every_space`).
* **Up to the static equivalence** (`OperationInvariant.upToStatics`): when
  contraction keeps the property, the property of the contraction is kept by
  the operations too.  This is the form in which the property is a property
  of the terms of the theory: equal terms have one contraction.
* **A count of constructors that is zero is such a property**
  (`tokens_invariant`): a step from a pattern without a counted constructor,
  at an ambient space without one and with no run in a space with one,
  reaches a pattern without one (`spacesAndRegions_stepAt_tokens`).
* **No step makes a variable atom**, at every ambient space
  (`spacesAndRegions_step_no_variableAtom`): the answers of every space for a
  subject without variable atom have none
  (`tokens_variable_of_mem_matchResults`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar instantiateBVarAt liftBVars)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)

/-! ## What matching binds, and what an instance is made of -/

/-- The values bound by a match of a list of first-order patterns against a
list of subjects with a property that parts inherit have the property. -/
theorem holds_of_matchedArgs {holds : Pattern → Prop} :
    ∀ {patterns : List Pattern},
      (∀ pattern ∈ patterns, ∀ {subject : Pattern} {bindings : Bindings},
        bindings ∈ matchPattern pattern subject → holds subject →
          ∀ entry ∈ bindings, holds entry.2) →
      ∀ {subjects : List Pattern} {bindings : Bindings},
        MatchArgsRel patterns subjects bindings → (∀ subject ∈ subjects, holds subject) →
          ∀ entry ∈ bindings, holds entry.2
  | [], _, _, _, related, _, entry, member => by
      cases related
      cases member
  | head :: tail, each, _, _, related, kept, entry, member => by
      cases related with
      | cons headRel tailRel merged =>
          rcases mem_of_mergeBindings merged entry member with inHead | inTail
          · exact each head (List.mem_cons_self ..) (matchRel_complete headRel)
              (kept _ (List.mem_cons_self ..)) entry inHead
          · exact holds_of_matchedArgs
              (fun pattern inTail' => each pattern (List.mem_cons_of_mem _ inTail')) tailRel
              (fun subject inSubjects => kept subject (List.mem_cons_of_mem _ inSubjects)) entry
              inTail

/-- **The values that a match of a first-order pattern binds are parts of its
subject**: they have every property of the subject that the arguments of an
application inherit from it. -/
theorem holds_of_matched {holds : Pattern → Prop}
    (inherited : ∀ (label : String) (arguments : List Pattern),
      holds (.apply label arguments) → ∀ argument ∈ arguments, holds argument)
    (pattern : Pattern) :
    isMatchCorrectAux pattern = true → ∀ {subject : Pattern} {bindings : Bindings},
      bindings ∈ matchPattern pattern subject → holds subject →
        ∀ entry ∈ bindings, holds entry.2 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ subject bindings matched _ entry member
      cases matchPattern_sound matched with
      | bvar => cases member
  | hfvar name =>
      intro _ subject bindings matched kept entry member
      rw [mem_matchPattern_fvar.mp matched] at member
      rw [List.mem_singleton.mp member]
      exact kept
  | happly label arguments ih =>
      intro exact subject bindings matched kept entry member
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      cases matchPattern_sound matched with
      | apply argsRel _ =>
          exact holds_of_matchedArgs
            (fun argument inArguments => ih argument inArguments (each argument inArguments))
            argsRel (inherited _ _ kept) entry member
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-- **An instance of a closed first-order pattern has every property that
its constructors build from their arguments**, when the values bound have
it. -/
theorem holds_applyBindings {holds : Pattern → Prop} {counted : String → Bool}
    (unbound : ∀ name : String, holds (.fvar name))
    (builds : ∀ (label : String) (arguments : List Pattern), counted label = false →
      (∀ argument ∈ arguments, holds argument) → holds (.apply label arguments))
    {bindings : Bindings} (values : ∀ entry ∈ bindings, holds entry.2) (pattern : Pattern) :
    isMatchCorrectAux pattern = true → pattern.isWellScopedAt 0 = true →
      tokens counted pattern = 0 → holds (applyBindings bindings pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ closed _
      simp [Pattern.isWellScopedAt] at closed
  | hfvar name =>
      intro _ _ _
      rw [applyBindings]
      split
      · next value found => exact values _ (List.mem_of_find?_eq_some found)
      · exact unbound name
  | happly label arguments ih =>
      intro exact closed zero
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      have closedEach : ∀ argument ∈ arguments, argument.isWellScopedAt 0 = true := by
        simp only [Pattern.isWellScopedAt] at closed
        exact (isWellScopedListAt_eq_true_iff 0 arguments).mp closed
      have unfolded : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by simp [applyBindings]
      rw [unfolded]
      refine builds label _ uncounted fun instance_ member => ?_
      obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
      exact ih argument inArguments (each argument inArguments) (closedEach argument inArguments)
        (clean argument inArguments)
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-- **The atoms that a space stores have every property of the space that
the arguments of an application inherit.** -/
theorem holds_of_mem_storedAtoms {holds : Pattern → Prop}
    (inherited : ∀ (label : String) (arguments : List Pattern),
      holds (.apply label arguments) → ∀ argument ∈ arguments, holds argument)
    (space : Pattern) : holds space → ∀ atom ∈ storedAtoms space, holds atom := by
  induction space using Pattern.inductionOn with
  | hbvar index => intro _ atom member; simp [storedAtoms] at member
  | hfvar name => intro _ atom member; simp [storedAtoms] at member
  | happly label arguments ih =>
      intro kept atom member
      have clean := inherited label arguments kept
      by_cases isAdd : label = "prime-space-add"
      · rw [storedAtoms, if_pos isAdd] at member
        rcases arguments with _ | ⟨stored, _ | ⟨rest, _ | ⟨extra, more⟩⟩⟩
        · simp [storedAtomsList] at member
        · simp [storedAtomsList] at member
        · rw [storedAtomsList] at member
          rcases List.mem_cons.mp member with rfl | inRest
          · exact clean _ (List.mem_cons_self ..)
          · exact ih rest (by simp) (clean rest (by simp)) atom inRest
        · simp [storedAtomsList] at member
      · rw [storedAtoms, if_neg isAdd] at member
        cases member
  | hlambda binder body _ => intro _ atom member; simp [storedAtoms] at member
  | hmultiLambda arity binders body _ => intro _ atom member; simp [storedAtoms] at member
  | hsubst body replacement _ _ => intro _ atom member; simp [storedAtoms] at member
  | hcollection kind elements rest _ => intro _ atom member; simp [storedAtoms] at member

/-- The arguments of a closed application are closed. -/
theorem wellScoped_of_mem_apply {depth : Nat} (label : String) (arguments : List Pattern)
    (closed : (Pattern.apply label arguments).isWellScopedAt depth = true) :
    ∀ argument ∈ arguments, argument.isWellScopedAt depth = true := by
  simp only [Pattern.isWellScopedAt] at closed
  exact (isWellScopedListAt_eq_true_iff depth arguments).mp closed

/-- Reading a stored atom as a side of a rule keeps it closed. -/
theorem isWellScopedAt_asRule (pattern : Pattern) :
    ∀ depth : Nat, pattern.isWellScopedAt depth = true →
      (asRule pattern).isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth closed; rw [asRule]; exact closed
  | hfvar name => intro depth closed; rw [asRule]; exact closed
  | happly label arguments ih =>
      intro depth closed
      by_cases isVariable : label = "prime-variable"
      · rw [asRule, if_pos isVariable]
        rfl
      · have each := wellScoped_of_mem_apply label arguments closed
        rw [asRule_apply_of_ne isVariable]
        simp only [Pattern.isWellScopedAt]
        rw [isWellScopedListAt_eq_true_iff]
        intro read member
        obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments depth (each argument inArguments)
  | hlambda binder body _ => intro depth closed; rw [asRule]; exact closed
  | hmultiLambda arity binders body _ => intro depth closed; rw [asRule]; exact closed
  | hsubst body replacement _ _ => intro depth closed; rw [asRule]; exact closed
  | hcollection kind elements rest _ => intro depth closed; rw [asRule]; exact closed

/-! ## The answers of a plain space for a sealed subject -/

/-- **The answers of a plain space for a subject that is sealed with plain
runs are sealed with plain runs.**  The space stores closed atoms without
quotation and without run; the values that a left side binds are parts of
the subject, and they are put where the right side has its variables, none
of which is beneath a quotation. -/
theorem sealedWithPlainRuns_of_mem_matchResults {space subject answer : Pattern} {depth : Nat}
    (plain : plainSpace space = true) (kept : SealedWithPlainRuns depth subject)
    (found : answer ∈ matchResults space subject) : SealedWithPlainRuns depth answer := by
  obtain ⟨closed, quiet⟩ := plainSpace_iff.mp plain
  obtain ⟨atom, stored, inAtom⟩ := List.mem_flatMap.mp found
  have atomClosed : atom.isWellScopedAt 0 = true :=
    holds_of_mem_storedAtoms (holds := fun pattern => pattern.isWellScopedAt 0 = true)
      wellScoped_of_mem_apply space closed atom stored
  have atomQuiet : tokens quoteOrRun atom = 0 := tokens_of_mem_storedAtoms space quiet atom stored
  unfold atomResults at inAtom
  split at inAtom
  · next left right viewed =>
      obtain rfl := eq_equation_of_viewEquation viewed
      obtain ⟨-, sides⟩ := tokens_apply_eq_zero_iff.mp atomQuiet
      have rightClosed : right.isWellScopedAt 0 = true :=
        wellScoped_of_mem_apply "=" [left, right] atomClosed right (by simp)
      split at inAtom
      · next exact =>
          simp only [Bool.and_eq_true] at exact
          obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp inAtom
          exact holds_applyBindings (holds := SealedWithPlainRuns depth) (counted := quoteOrRun)
            (fun name => ⟨by simp [sealedAt, binderSafeAt], by rw [runsPlain]⟩)
            (fun label arguments other each =>
              (sealedWithPlainRuns_apply_iff other depth arguments).mpr each)
            (holds_of_matched (holds := SealedWithPlainRuns depth)
              (fun label arguments both => both.of_mem_apply) (asRule left) exact.1 matched kept)
            (asRule right) exact.2 (isWellScopedAt_asRule right 0 rightClosed)
            (tokens_asRule_eq_zero right (sides right (by simp)))
      · cases inAtom
  · cases inAtom

/-! ## A property that the operations of a step keep -/

/-- **A property of patterns, by the number of binders around them, that the
operations of a step keep**, at the spaces with the property `space`:

* an application, an abstraction and a product have it exactly when their
  parts have it, the body beneath one more binder;
* a run has it exactly when its space has the property of spaces and its
  subject has it;
* the instantiation of a binder and the release of a dropped quotation keep
  it;
* the answers of a space with the property of spaces, for a subject that has
  it, have it. -/
structure OperationInvariant (holds : Nat → Pattern → Prop) (space : Pattern → Prop) : Prop where
  application : ∀ {depth : Nat} {function argument : Pattern},
    holds depth (.apply "App" [function, argument]) ↔ holds depth function ∧ holds depth argument
  abstraction : ∀ {depth : Nat} {domain body : Pattern} {binder : Option String},
    holds depth (.apply "Lam" [domain, .lambda binder body]) ↔
      holds depth domain ∧ holds (depth + 1) body
  product : ∀ {depth : Nat} {domain body : Pattern} {binder : Option String},
    holds depth (.apply "Pi" [domain, .lambda binder body]) ↔
      holds depth domain ∧ holds (depth + 1) body
  run : ∀ {depth : Nat} {region subject : Pattern},
    holds depth (runPattern region subject) ↔ space region ∧ holds depth subject
  instantiate : ∀ {depth : Nat} {argument body : Pattern},
    holds depth argument → holds (depth + 1) body → holds depth (instantiateBVar argument body)
  release : ∀ {depth : Nat} {atom : Pattern},
    holds depth (dropped (quoted atom)) → holds depth atom
  answers : ∀ {depth : Nat} {region subject answer : Pattern}, space region →
    holds depth subject → answer ∈ matchResults (contract region) (contract subject) →
      holds depth answer

/-- **One induction over the thirty-three rewrites**: a property that the
operations of a step keep is kept by every step, in every language with the
rewrites of `allHeaded`, under every guard, at every ambient space whose
answers for a subject with the property have it. -/
theorem OperationInvariant.stepAt {holds : Nat → Pattern → Prop} {space : Pattern → Prop}
    (invariant : OperationInvariant holds space) {lang : LanguageDef}
    (rules : lang.rewrites = allHeaded.rewrites) {admits : Pattern → Bool} {ambientSpace : Pattern}
    (ambient : ∀ {depth : Nat} {subject answer : Pattern}, holds depth subject →
      answer ∈ matchResults (contract ambientSpace) (contract subject) → holds depth answer) :
    ∀ (fuel : Nat) {depth : Nat} {source target : Pattern},
      StepAt (regionEvaluator admits ambientSpace) lang fuel source target →
        holds depth source → holds depth target := by
  intro fuel
  induction fuel with
  | zero => intro depth source target step; cases step
  | succ fuel ih =>
      intro depth source target step kept
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
      rw [rules] at member
      rcases mem_allHeaded_rewrites.mp member with plain | root | spatial | runRoot | beneath
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
        rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨domain, binder, body, argument, rfl, applied⟩ := beta_inv matched premises
          rw [applied]
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp kept
          exact invariant.instantiate argumentKept (invariant.abstraction.mp functionKept).2
        · obtain ⟨function, argument, next, rfl, inner, applied⟩ :=
            appFunction_inv matched premises
          rw [applied]
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp kept
          exact invariant.application.mpr ⟨ih inner functionKept, argumentKept⟩
        · obtain ⟨function, argument, next, rfl, inner, applied⟩ :=
            appArgument_inv matched premises
          rw [applied]
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp kept
          exact invariant.application.mpr ⟨functionKept, ih inner argumentKept⟩
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piDomain_inv matched premises
          rw [applied]
          obtain ⟨domainKept, bodyKept⟩ := invariant.product.mp kept
          exact invariant.product.mpr ⟨ih inner domainKept, bodyKept⟩
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := piBody_inv matched premises
          rw [applied]
          obtain ⟨domainKept, bodyKept⟩ := invariant.product.mp kept
          exact invariant.product.mpr ⟨domainKept, ih inner bodyKept⟩
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ :=
            lamDomain_inv matched premises
          rw [applied]
          obtain ⟨domainKept, bodyKept⟩ := invariant.abstraction.mp kept
          exact invariant.abstraction.mpr ⟨ih inner domainKept, bodyKept⟩
        · obtain ⟨domain, binder, body, next, rfl, inner, applied⟩ := lamBody_inv matched premises
          rw [applied]
          obtain ⟨domainKept, bodyKept⟩ := invariant.abstraction.mp kept
          exact invariant.abstraction.mpr ⟨domainKept, ih inner bodyKept⟩
        · obtain ⟨atom, rfl, applied⟩ := release_inv matched premises
          rw [applied]
          exact invariant.release kept
      · obtain ⟨name, label, parameters, rfl, exact, -⟩ := headedRoots_shape rule root
        obtain ⟨answer, found, applied⟩ := headedRoot_inv exact matched premises
        rw [applied]
        exact ambient kept (mem_admittedAnswers.mp found).2
      · simp only [spatialCongruences, List.mem_cons, List.not_mem_nil, or_false] at spatial
        rcases spatial with rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨region, function, argument, next, rfl, inner, applied⟩ :=
            runAppFunction_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp subjectKept
          have moved :=
            (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, functionKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.application.mpr ⟨moved, argumentKept⟩⟩
        · obtain ⟨region, function, argument, next, rfl, inner, applied⟩ :=
            runAppArgument_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp subjectKept
          have moved :=
            (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, argumentKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.application.mpr ⟨functionKept, moved⟩⟩
        · obtain ⟨region, domain, binder, body, next, rfl, inner, applied⟩ :=
            runPiDomain_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨domainKept, bodyKept⟩ := invariant.product.mp subjectKept
          have moved := (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, domainKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.product.mpr ⟨moved, bodyKept⟩⟩
        · obtain ⟨region, domain, binder, body, next, rfl, inner, applied⟩ :=
            runPiBody_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨domainKept, bodyKept⟩ := invariant.product.mp subjectKept
          have moved := (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, bodyKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.product.mpr ⟨domainKept, moved⟩⟩
        · obtain ⟨region, domain, binder, body, next, rfl, inner, applied⟩ :=
            runLamDomain_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨domainKept, bodyKept⟩ := invariant.abstraction.mp subjectKept
          have moved := (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, domainKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.abstraction.mpr ⟨moved, bodyKept⟩⟩
        · obtain ⟨region, domain, binder, body, next, rfl, inner, applied⟩ :=
            runLamBody_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨domainKept, bodyKept⟩ := invariant.abstraction.mp subjectKept
          have moved := (invariant.run.mp (ih inner (invariant.run.mpr ⟨regionKept, bodyKept⟩))).2
          exact invariant.run.mpr ⟨regionKept, invariant.abstraction.mpr ⟨domainKept, moved⟩⟩
      · obtain ⟨name, rootName, label, parameters, rfl, -, exact⟩ :=
          headedRunRoots_shape rule runRoot
        obtain ⟨region, subject, answer, bindings, rfl, -, -, -, found, applied⟩ :=
          headedRunRoot_inv exact matched premises
        rw [applied]
        obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
        exact invariant.run.mpr ⟨regionKept,
          invariant.answers regionKept subjectKept (mem_admittedAnswers.mp found).2⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at beneath
        rcases beneath with rfl | rfl | rfl
        · obtain ⟨region, domain, binder, body, argument, rfl, applied⟩ :=
            runBeta_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          obtain ⟨functionKept, argumentKept⟩ := invariant.application.mp subjectKept
          exact invariant.run.mpr ⟨regionKept,
            invariant.instantiate argumentKept (invariant.abstraction.mp functionKept).2⟩
        · obtain ⟨region, atom, rfl, applied⟩ := runRelease_inv matched premises
          rw [applied]
          obtain ⟨regionKept, subjectKept⟩ := invariant.run.mp kept
          exact invariant.run.mpr ⟨regionKept, invariant.release subjectKept⟩
        · obtain ⟨outer, region, subject, next, rfl, inner, applied⟩ :=
            runBeneathRun_inv matched premises
          rw [applied]
          obtain ⟨outerKept, innerKept⟩ := invariant.run.mp kept
          exact invariant.run.mpr ⟨outerKept, ih inner innerKept⟩

/-- **Such a property is kept by every step at an ambient space with the
property of spaces.** -/
theorem OperationInvariant.step {holds : Nat → Pattern → Prop} {space : Pattern → Prop}
    (invariant : OperationInvariant holds space) {lang : LanguageDef}
    (rules : lang.rewrites = allHeaded.rewrites) {admits : Pattern → Bool} {ambientSpace : Pattern}
    (ambient : space ambientSpace) {depth : Nat} {source target : Pattern}
    (moved : Step (regionEvaluator admits ambientSpace) lang source target)
    (kept : holds depth source) : holds depth target := by
  obtain ⟨fuel, bounded⟩ := moved
  exact invariant.stepAt rules
    (fun subjectKept found => invariant.answers ambient subjectKept found) fuel bounded kept

/-! ## Sealed with plain runs is kept, at plain spaces -/

/-- An abstraction of the pattern syntax is sealed with plain runs exactly
when its body is, beneath one more binder. -/
theorem sealedWithPlainRuns_lambda (depth : Nat) (binder : Option String) (body : Pattern) :
    SealedWithPlainRuns depth (.lambda binder body) ↔ SealedWithPlainRuns (depth + 1) body := by
  unfold SealedWithPlainRuns
  rw [sealedAt_lambda, runsPlain]

/-- **Sealed with plain runs is a property that the operations of a step
keep, at the plain spaces.** -/
theorem sealedWithPlainRuns_invariant :
    OperationInvariant SealedWithPlainRuns (fun space => plainSpace space = true) where
  application := by
    intro depth function argument
    rw [sealedWithPlainRuns_apply_iff (by decide)]
    simp
  abstraction := by
    intro depth domain body binder
    rw [sealedWithPlainRuns_apply_iff (by decide)]
    simp [sealedWithPlainRuns_lambda]
  product := by
    intro depth domain body binder
    rw [sealedWithPlainRuns_apply_iff (by decide)]
    simp [sealedWithPlainRuns_lambda]
  run := sealedWithPlainRuns_runPattern _ _ _
  instantiate := by
    intro depth argument body argumentKept bodyKept
    exact ⟨binderSafeAt_instantiateBVar "prime-quote" argument depth argumentKept.1 body bodyKept.1,
      runsPlain_instantiateBVarAt argumentKept.2 body 0 bodyKept.2⟩
  release := by
    intro depth atom kept
    have inner := kept.of_mem_apply (quoted atom) (List.mem_singleton.mpr rfl)
    exact inner.of_mem_apply atom (by simp)
  answers := by
    intro depth region subject answer plain kept found
    rw [contract_of_plainSpace plain] at found
    exact sealedWithPlainRuns_of_mem_matchResults plain kept.contract found

/-! ## The hypothesis on the space is needed -/

/-- **The space of the rule `$0 ⟶ *@$0`**: every atom has, as an answer, the
dropped quotation of itself.  Its right side has its variable beneath a
quotation. -/
def quotingSpace : Pattern :=
  spaceOfAtoms [.apply "=" [variableAtom (numeral 0), dropped (quoted (variableAtom (numeral 0)))]]

/-- It is not plain: it stores a quotation. -/
theorem not_plainSpace_quotingSpace : plainSpace quotingSpace = false := by decide +kernel

/-- An abstraction whose body mentions the bound variable outside every
quotation: `λ x. (() x)`. -/
def mentionsItsVariable : Pattern :=
  .apply "Lam" [unitAtom, .lambda none (.apply "App" [unitAtom, .bvar 0])]

/-- The abstraction whose body drops the quotation of that body:
`λ x. *@(() x)`. -/
def quotesItsVariable : Pattern :=
  .apply "Lam" [unitAtom, .lambda none (dropped (quoted (.apply "App" [unitAtom, .bvar 0])))]

/-- What the quoting space answers for a pattern that contraction fixes. -/
theorem quotingSpace_answers {subject : Pattern} (fixed : contract subject = subject) :
    dropped (quoted subject) ∈ admittedAnswers anySubject quotingSpace subject := by
  refine mem_admittedAnswers.mpr ⟨rfl, ?_⟩
  rw [show contract quotingSpace = quotingSpace by decide +kernel, fixed]
  refine mem_matchResults_spaceOfAtoms.mpr ⟨_, List.mem_singleton.mpr rfl, ?_⟩
  have leftRule : asRule (variableAtom (numeral 0)) = .fvar (metaName 0) := asRule_variableAtom 0
  have rightRule : asRule (dropped (quoted (variableAtom (numeral 0)))) =
      dropped (quoted (.fvar (metaName 0))) := by
    rw [dropped, asRule_apply_of_ne (by decide)]
    simp only [List.map_cons, List.map_nil]
    rw [quoted, asRule_apply_of_ne (by decide)]
    simp only [List.map_cons, List.map_nil, leftRule]
    rfl
  rw [atomResults_equation _ (by rw [leftRule]; rfl) (by rw [rightRule]; decide), leftRule,
    rightRule]
  simp [matchPattern, applyBindings, dropped, quoted]

/-- **At the quoting space a sealed abstraction steps to one that is not
sealed.**  The step is a root step beneath the binder: the body is matched by
the variable of the rule, and put beneath the quotation of its right side
with the bound variable in it. -/
theorem quotingSpace_unseals :
    SealedWithPlainRuns 0 mentionsItsVariable ∧
      Step (regionEvaluator anySubject quotingSpace) spacesAndRegions mentionsItsVariable
        quotesItsVariable ∧
        sealedAt 0 quotesItsVariable = false := by
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ?_, by decide +kernel⟩
  obtain ⟨fuel, inner⟩ := assembledOver_root_step (admits := anySubject) allHeaded.name
    (constructors := atomsReduce.terms) (constructor := applicationConstructor) (by decide)
    (by decide) (arguments := [unitAtom, .bvar 0]) (by decide)
    (quotingSpace_answers (subject := .apply "App" [unitAtom, .bvar 0]) (by decide +kernel))
  exact ⟨fuel + 1, step_lamBody
    (by rw [show spacesAndRegions.rewrites = allHeaded.rewrites from spacesAndRegions_rewrites]
        exact allHeaded_mem_plain (by simp)) unitAtom none inner⟩

/-- **Sealing with every space is no property that the operations of a step
keep**: a space may store a rule that puts its variable beneath a
quotation. -/
theorem sealing_not_invariant_at_every_space :
    ¬ OperationInvariant SealedWithPlainRuns (fun _ => True) := by
  intro invariant
  obtain ⟨kept, moved, open_⟩ := quotingSpace_unseals
  have reached := invariant.step spacesAndRegions_rewrites trivial moved kept
  rw [reached.1] at open_
  cases open_

/-! ## Up to the static equivalence -/

/-- **A property that the operations of a step keep and that contraction
keeps, read on the contraction, is kept by the operations of a step**, at the
spaces whose contraction has the property of spaces.  Equal terms have one
contraction, so this is the property as a property of the terms of the
theory. -/
theorem OperationInvariant.upToStatics {holds : Nat → Pattern → Prop} {space : Pattern → Prop}
    (invariant : OperationInvariant holds space)
    (contracted : ∀ {depth : Nat} {pattern : Pattern}, holds depth pattern →
      holds depth (contract pattern)) :
    OperationInvariant (fun depth pattern => holds depth (contract pattern))
      (fun region => space (contract region)) where
  application := by
    intro depth function argument
    rw [contract_apply_of_ne (by decide)]
    exact invariant.application
  abstraction := by
    intro depth domain body binder
    rw [contract_apply_of_ne (by decide)]
    simp only [List.map_cons, List.map_nil, contract]
    exact invariant.abstraction
  product := by
    intro depth domain body binder
    rw [contract_apply_of_ne (by decide)]
    simp only [List.map_cons, List.map_nil, contract]
    exact invariant.product
  run := by
    intro depth region subject
    rw [runPattern, contract_apply_of_ne (by decide)]
    exact invariant.run
  instantiate := by
    intro depth argument body argumentKept bodyKept
    show holds depth (contract (instantiateBVarAt 0 argument body))
    rw [← contract_instantiateBVarAt_contract]
    exact contracted (invariant.instantiate argumentKept bodyKept)
  release := by
    intro depth atom kept
    rw [contract_dropped, contract_quoted] at kept
    rcases contractRoot_quote_cases (contract atom) with ⟨name, isDrop, value⟩ | plain
    · rw [value] at kept
      show holds depth (contract atom)
      rw [isDrop]
      exact kept
    · rw [plain] at kept
      exact invariant.release kept
  answers := by
    intro depth region subject answer regionKept subjectKept found
    rw [← contract_contract region, ← contract_contract subject] at found
    exact contracted (invariant.answers regionKept subjectKept found)

/-- **Sealed with plain runs up to the static equivalence**: the contraction
is sealed with plain runs.  It is kept by the operations of a step, at the
spaces whose contraction is plain. -/
theorem sealedUpToStatics_invariant :
    OperationInvariant (fun depth pattern => SealedWithPlainRuns depth (contract pattern))
      (fun space => plainSpace (contract space) = true) :=
  sealedWithPlainRuns_invariant.upToStatics fun kept => kept.contract

/-! ## A count of constructors that is zero -/

/-- **A count of constructors that is zero is a property that the operations
of a step keep**, at the spaces where it is zero, when the count counts none
of application, abstraction, product, the run, quotation and dropping. -/
theorem tokens_invariant {counted : String → Bool} (application : counted "App" = false)
    (abstraction : counted "Lam" = false) (product : counted "Pi" = false)
    (run : counted "prime-run" = false) (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) :
    OperationInvariant (fun _ pattern => tokens counted pattern = 0)
      (fun space => tokens counted space = 0) where
  application := by
    intro depth function argument
    rw [tokens_apply_eq_zero_iff]
    simp [application]
  abstraction := by
    intro depth domain body binder
    rw [tokens_apply_eq_zero_iff]
    simp [abstraction, tokens]
  product := by
    intro depth domain body binder
    rw [tokens_apply_eq_zero_iff]
    simp [product, tokens]
  run := by
    intro depth region subject
    rw [runPattern, tokens_apply_eq_zero_iff]
    simp [run]
  instantiate := by
    intro depth argument body argumentClean bodyClean
    exact tokens_instantiateBVarAt_eq_zero argumentClean body 0 bodyClean
  release := by
    intro depth atom clean
    obtain ⟨-, outer⟩ := tokens_apply_eq_zero_iff.mp (show tokens counted
      (.apply "prime-drop" [.apply "prime-quote" [atom]]) = 0 from clean)
    obtain ⟨-, inner⟩ := tokens_apply_eq_zero_iff.mp (outer (.apply "prime-quote" [atom]) (by simp))
    exact inner atom (by simp)
  answers := by
    intro depth region subject answer regionClean subjectClean found
    exact tokens_of_mem_matchResults (by rw [tokens_contract quote drop]; exact regionClean)
      (by rw [tokens_contract quote drop]; exact subjectClean) answer found

/-- **A step of the candidate builds no constructor that it was not given**:
from a pattern without a counted constructor, at an ambient space without
one, it reaches a pattern without one, for every count that counts none of
application, abstraction, product, the run, quotation and dropping. -/
theorem spacesAndRegions_stepAt_tokens {counted : String → Bool}
    (application : counted "App" = false) (abstraction : counted "Lam" = false)
    (product : counted "Pi" = false) (run : counted "prime-run" = false)
    (quote : counted "prime-quote" = false) (drop : counted "prime-drop" = false)
    {admits : Pattern → Bool} {ambientSpace : Pattern}
    (cleanSpace : tokens counted ambientSpace = 0) {source target : Pattern}
    (moved : Step (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (clean : tokens counted source = 0) : tokens counted target = 0 :=
  (tokens_invariant application abstraction product run quote drop).step
    (depth := 0) spacesAndRegions_rewrites cleanSpace moved clean

/-! ## No step makes a variable atom -/

/-- The label of the variable atom. -/
def isVariableAtom (label : String) : Bool := label == "prime-variable"

/-- **Positive**: the variable atom. -/
theorem isVariableAtom_variable : isVariableAtom "prime-variable" = true := by decide

/-- **Negative**: the symbol. -/
theorem not_isVariableAtom_symbol : isVariableAtom "prime-symbol" = false := by decide

/-- **A stored atom read as a first-order side of a rule has no variable
atom**: each of them has become a variable of the rule. -/
theorem tokens_variable_asRule (pattern : Pattern) :
    isMatchCorrectAux (asRule pattern) = true → tokens isVariableAtom (asRule pattern) = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [asRule]; rfl
  | hfvar name => intro _; rw [asRule]; rfl
  | happly label arguments ih =>
      intro exact
      by_cases isVariable : label = "prime-variable"
      · rw [asRule, if_pos isVariable]
        rfl
      · rw [asRule_apply_of_ne isVariable] at exact ⊢
        have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
        refine tokens_apply_eq_zero_iff.mpr ⟨by simpa [isVariableAtom] using isVariable,
          fun read member => ?_⟩
        obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments (each _ member)
  | hlambda binder body _ => intro exact; rw [asRule] at exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ =>
      intro exact; rw [asRule] at exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ =>
      intro exact; rw [asRule] at exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ =>
      intro exact; rw [asRule] at exact; simp [isMatchCorrectAux] at exact

/-- **The answers of every space for a subject without variable atom have
none.**  Nothing is asked of the space: the variable atoms that it stores are
read as the variables of its rules. -/
theorem tokens_variable_of_mem_matchResults {space subject answer : Pattern}
    (clean : tokens isVariableAtom subject = 0) (found : answer ∈ matchResults space subject) :
    tokens isVariableAtom answer = 0 := by
  obtain ⟨atom, -, inAtom⟩ := List.mem_flatMap.mp found
  unfold atomResults at inAtom
  split at inAtom
  · next left right viewed =>
      split at inAtom
      · next exact =>
          simp only [Bool.and_eq_true] at exact
          obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp inAtom
          exact tokens_applyBindings_eq_zero
            (tokens_of_matched (asRule left) exact.1 matched clean) (asRule right) exact.2
            (tokens_variable_asRule right exact.2)
      · cases inAtom
  · cases inAtom

/-- **A step of the candidate makes no variable atom**, under every guard
and at every ambient space: from a pattern without variable atom it reaches a
pattern without one. -/
theorem spacesAndRegions_step_no_variableAtom {admits : Pattern → Bool} {ambientSpace : Pattern}
    {source target : Pattern}
    (moved : Step (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (clean : tokens isVariableAtom source = 0) : tokens isVariableAtom target = 0 := by
  obtain ⟨fuel, bounded⟩ := moved
  exact (tokens_invariant (counted := isVariableAtom) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).stepAt (depth := 0) spacesAndRegions_rewrites
    (fun subjectClean found => tokens_variable_of_mem_matchResults
      (by rw [tokens_contract (by decide) (by decide)]; exact subjectClean) found)
    fuel bounded clean

#print axioms holds_of_matched
#print axioms holds_applyBindings
#print axioms holds_of_mem_storedAtoms
#print axioms isWellScopedAt_asRule
#print axioms sealedWithPlainRuns_of_mem_matchResults
#print axioms OperationInvariant.stepAt
#print axioms OperationInvariant.step
#print axioms sealedWithPlainRuns_invariant
#print axioms not_plainSpace_quotingSpace
#print axioms quotingSpace_answers
#print axioms quotingSpace_unseals
#print axioms sealing_not_invariant_at_every_space
#print axioms OperationInvariant.upToStatics
#print axioms sealedUpToStatics_invariant
#print axioms tokens_invariant
#print axioms spacesAndRegions_stepAt_tokens
#print axioms tokens_variable_asRule
#print axioms tokens_variable_of_mem_matchResults
#print axioms spacesAndRegions_step_no_variableAtom

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
