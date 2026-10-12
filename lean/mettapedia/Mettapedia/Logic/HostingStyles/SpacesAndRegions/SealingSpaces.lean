import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedSteps

/-!
# The ambient spaces at which a step keeps a term sealed

A step at the root replaces a pattern by an instance of a right side that
the ambient space stores.  The values of the instance are parts of the
pattern.  A part beneath a quotation of a sealed pattern is closed; a part
outside every quotation is sealed beneath the binders around the pattern, and
need not be closed.  So the instance is sealed when the right side puts
beneath a quotation only values that the left side found beneath a quotation.

* **A space quotes only what was quoted** (`QuotesOnlyQuoted`) when each
  right side that it stores is closed, has no run, and has beneath a
  quotation only variables that its left side has beneath a quotation
  (`variableUses`).
* **The answers of such a space for a sealed subject are sealed**
  (`QuotesOnlyQuoted.sealed_of_mem_matchResults`).  A match rebuilds its
  subject, so the value at each use of a variable of the left side is as
  sealed as that use asks (`uses_sealed_of_instance`); and an instance whose
  values are so is sealed (`sealedWithPlainRuns_instance`).  So **a step of
  the candidate, at an ambient space whose contraction quotes only what was
  quoted, keeps a pattern sealed with plain runs**: as it is written
  (`spacesAndRegions_step_sealed`), and up to the static equivalence
  (`spacesAndRegions_step_sealedUpToStatics`).
* The plain spaces are such spaces (`quotesOnlyQuoted_of_plainSpace`).  So
  are a space that stores a closed quotation and the space of the rule
  `*@$0 ⟶ *@$0`, which are not plain (`quotesOnlyQuoted_closedQuotation`,
  `quotesOnlyQuoted_requoting`).  The space of the rule `$0 ⟶ *@$0` is none:
  its variable is beneath a quotation on the right alone
  (`not_quotesOnlyQuoted_quotingSpace`), and there a step unseals an
  abstraction (`quotingSpace_unseals`).
* **The runs of a sealed pattern have plain spaces, and a condition on them
  is needed too** (`quotingRun_unseals`): at the empty ambient space an
  abstraction that is sealed, with a run in the space of that rule in its
  body, steps to one that is not sealed.
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
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)

/-! ## Where a side of a rule has its variables -/

mutual
  /-- **The uses of the variables of a side of a rule**, each with whether it
  is beneath a quotation; `beneath` says whether the side itself is. -/
  def variableUses (beneath : Bool) : Pattern → List (String × Bool)
    | .bvar _ => []
    | .fvar name => [(name, beneath)]
    | .apply label arguments =>
        variableUsesList (beneath || (label == "prime-quote" && arguments.length == 1)) arguments
    | .lambda _ _ => []
    | .multiLambda _ _ _ => []
    | .subst _ _ => []
    | .collection _ _ _ => []

  /-- The uses in the patterns of a list. -/
  def variableUsesList (beneath : Bool) : List Pattern → List (String × Bool)
    | [] => []
    | pattern :: patterns => variableUses beneath pattern ++ variableUsesList beneath patterns
end

/-- **Positive**: a variable in a dropped quotation is used beneath a
quotation. -/
theorem variableUses_dropQuote :
    variableUses false (dropped (quoted (.fvar "x"))) = [("x", true)] := by decide +kernel

/-- **Negative**: the variables of an application are used outside every
quotation. -/
theorem variableUses_application :
    variableUses false (.apply "App" [.fvar "x", .fvar "y"]) = [("x", false), ("y", false)] := by
  decide +kernel

theorem mem_variableUsesList {use : String × Bool} {beneath : Bool} :
    ∀ {patterns : List Pattern}, use ∈ variableUsesList beneath patterns ↔
      ∃ pattern ∈ patterns, use ∈ variableUses beneath pattern
  | [] => by simp [variableUsesList]
  | pattern :: patterns => by
      rw [variableUsesList, List.mem_append, mem_variableUsesList (patterns := patterns)]
      simp

/-- The uses in a quotation are beneath a quotation. -/
theorem variableUses_quotation (beneath : Bool) (body : Pattern) :
    variableUses beneath (.apply "prime-quote" [body]) = variableUses true body := by
  simp [variableUses, variableUsesList]

/-- The uses in an application that is no quotation are those of its
arguments. -/
theorem variableUses_apply_of_not_quotation {label : String} {arguments : List Pattern}
    (other : ¬ (label = "prime-quote" ∧ arguments.length = 1)) (beneath : Bool) :
    variableUses beneath (.apply label arguments) = variableUsesList beneath arguments := by
  have flag : (label == "prime-quote" && arguments.length == 1) = false := by
    simpa using other
  rw [variableUses, flag, Bool.or_false]

/-- **The number of binders beneath which the value at a use is sealed**:
none where the use is beneath a quotation, those around the pattern where it
is outside every quotation. -/
def sealingDepth (depth : Nat) (beneath : Bool) : Nat := bif beneath then 0 else depth

/-- **Positive**: beneath a quotation, no binder. -/
theorem sealingDepth_beneath (depth : Nat) : sealingDepth depth true = 0 := rfl

/-- **Negative**: outside every quotation, the binders around the pattern. -/
theorem sealingDepth_outside (depth : Nat) : sealingDepth depth false = depth := rfl

/-! ## Instances of a side of a rule -/

/-- The instance of a pattern variable is a value bound to it, or the
variable. -/
theorem applyBindings_fvar_cases (bindings : Bindings) (name : String) :
    (∃ entry ∈ bindings, applyBindings bindings (.fvar name) = entry.2) ∨
      applyBindings bindings (.fvar name) = .fvar name := by
  simp only [applyBindings]
  cases found : bindings.find? (fun pair => pair.1 == name) with
  | none => exact .inr rfl
  | some entry => exact .inl ⟨entry, List.mem_of_find?_eq_some found, rfl⟩

/-- An application that is no quotation is sealed exactly when its arguments
are. -/
theorem sealedAt_apply_of_not_quotation {label : String} {arguments : List Pattern}
    (other : ¬ (label = "prime-quote" ∧ arguments.length = 1)) (depth : Nat) :
    sealedAt depth (.apply label arguments) = true ↔
      ∀ argument ∈ arguments, sealedAt depth argument = true := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rw [← binderSafeListAt_eq_true_iff]
    rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
    · simp [sealedAt, binderSafeAt, binderSafeListAt]
    · exact absurd ⟨rfl, rfl⟩ other
    · exact Iff.rfl
  · exact sealedAt_apply_of_ne isQuote depth arguments

/-- **What a sealed instance says of its values**: when an instance of a
first-order pattern is sealed with plain runs, so is the value at each use of
a variable, and beneath no binder where the use is beneath a quotation. -/
theorem uses_sealed_of_instance {depth : Nat} {bindings : Bindings} (pattern : Pattern) :
    ∀ beneath : Bool, isMatchCorrectAux pattern = true →
      SealedWithPlainRuns (sealingDepth depth beneath) (applyBindings bindings pattern) →
        ∀ use ∈ variableUses beneath pattern,
          SealedWithPlainRuns (sealingDepth depth use.2)
            (applyBindings bindings (.fvar use.1)) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro beneath _ _ use member
      simp [variableUses] at member
  | hfvar name =>
      intro beneath _ kept use member
      rw [variableUses, List.mem_singleton] at member
      rw [member]
      exact kept
  | happly label arguments ih =>
      intro beneath exact kept use member
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      have unfolded : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by simp [applyBindings]
      rw [unfolded] at kept
      by_cases isQuotation : label = "prime-quote" ∧ arguments.length = 1
      · obtain ⟨rfl, length⟩ := isQuotation
        obtain ⟨body, rfl⟩ := List.length_eq_one_iff.mp length
        rw [variableUses_quotation] at member
        have inner : SealedWithPlainRuns 0 (applyBindings bindings body) := by
          have safe := kept.1
          rw [List.map_cons, List.map_nil,
            show Pattern.apply "prime-quote" [applyBindings bindings body] =
              quoted (applyBindings bindings body) from rfl, sealedAt_quoted] at safe
          exact ⟨safe, ((runsPlain_apply_of_ne (by decide) _).mp kept.2) _
            (List.mem_map_of_mem (List.mem_singleton.mpr rfl))⟩
        exact ih body (List.mem_singleton.mpr rfl) true (each body (List.mem_singleton.mpr rfl))
          inner use member
      · rw [variableUses_apply_of_not_quotation isQuotation, mem_variableUsesList] at member
        obtain ⟨argument, inArguments, inner⟩ := member
        exact ih argument inArguments beneath (each argument inArguments)
          (kept.of_mem_apply _ (List.mem_map_of_mem inArguments)) use inner
  | hlambda binder body _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro beneath exact; simp [isMatchCorrectAux] at exact

/-- **An instance of a side of a rule is sealed with plain runs**, when the
side is closed and has no run, and the value at each use of a variable is
sealed with plain runs: beneath no binder where the use is beneath a
quotation. -/
theorem sealedWithPlainRuns_instance {depth : Nat} {bindings : Bindings} (pattern : Pattern) :
    ∀ beneath : Bool, isMatchCorrectAux pattern = true → pattern.isWellScopedAt 0 = true →
      tokens runLabel pattern = 0 →
        (∀ use ∈ variableUses beneath pattern,
          SealedWithPlainRuns (sealingDepth depth use.2)
            (applyBindings bindings (.fvar use.1))) →
          SealedWithPlainRuns (sealingDepth depth beneath) (applyBindings bindings pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro beneath _ closed
      simp [Pattern.isWellScopedAt] at closed
  | hfvar name =>
      intro beneath _ _ _ values
      exact values (name, beneath) (by rw [variableUses]; exact List.mem_singleton.mpr rfl)
  | happly label arguments ih =>
      intro beneath exact closed noRun values
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      have closedEach := wellScoped_of_mem_apply label arguments closed
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp noRun
      have notRun : label ≠ "prime-run" := by
        rintro rfl
        exact absurd uncounted (by decide)
      have unfolded : applyBindings bindings (.apply label arguments) =
          .apply label (arguments.map (applyBindings bindings)) := by simp [applyBindings]
      rw [unfolded]
      by_cases isQuotation : label = "prime-quote" ∧ arguments.length = 1
      · obtain ⟨rfl, length⟩ := isQuotation
        obtain ⟨body, rfl⟩ := List.length_eq_one_iff.mp length
        have inner : SealedWithPlainRuns 0 (applyBindings bindings body) :=
          ih body (List.mem_singleton.mpr rfl) true (each body (List.mem_singleton.mpr rfl))
            (closedEach body (List.mem_singleton.mpr rfl)) (clean body (List.mem_singleton.mpr rfl))
            fun use member => values use (by rw [variableUses_quotation]; exact member)
        rw [List.map_cons, List.map_nil]
        refine ⟨?_, (runsPlain_apply_of_ne (by decide) _).mpr fun part inside => ?_⟩
        · rw [show Pattern.apply "prime-quote" [applyBindings bindings body] =
            quoted (applyBindings bindings body) from rfl, sealedAt_quoted]
          exact inner.1
        · rw [List.mem_singleton.mp inside]
          exact inner.2
      · have parts : ∀ instance_ ∈ arguments.map (applyBindings bindings),
            SealedWithPlainRuns (sealingDepth depth beneath) instance_ := by
          intro instance_ member
          obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
          exact ih argument inArguments beneath (each argument inArguments)
            (closedEach argument inArguments) (clean argument inArguments)
            fun use inner => values use (by
              rw [variableUses_apply_of_not_quotation isQuotation, mem_variableUsesList]
              exact ⟨argument, inArguments, inner⟩)
        exact ⟨(sealedAt_apply_of_not_quotation (by simpa using isQuotation) _).mpr
            fun instance_ member => (parts instance_ member).1,
          (runsPlain_apply_of_ne notRun _).mpr fun instance_ member =>
            (parts instance_ member).2⟩
  | hlambda binder body _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro beneath exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro beneath exact; simp [isMatchCorrectAux] at exact

/-! ## The spaces that quote only what was quoted -/

/-- **A space that quotes only what was quoted**: each right side that it
stores is closed, has no run, and has beneath a quotation only variables that
its left side has beneath a quotation. -/
def QuotesOnlyQuoted (space : Pattern) : Prop :=
  ∀ left right : Pattern, .apply "=" [left, right] ∈ storedAtoms space →
    right.isWellScopedAt 0 = true ∧ tokens runLabel right = 0 ∧
      ∀ name : String, (name, true) ∈ variableUses false (asRule right) →
        (name, true) ∈ variableUses false (asRule left)

/-- **The answers of a space that quotes only what was quoted, for a subject
that is sealed with plain runs, are sealed with plain runs.**  A match
rebuilds the subject, so a value that the left side finds beneath a quotation
is sealed beneath no binder; the right side puts beneath a quotation only
such values. -/
theorem QuotesOnlyQuoted.sealed_of_mem_matchResults {space subject answer : Pattern}
    {depth : Nat} (safe : QuotesOnlyQuoted space) (kept : SealedWithPlainRuns depth subject)
    (found : answer ∈ matchResults space subject) : SealedWithPlainRuns depth answer := by
  obtain ⟨atom, stored, inAtom⟩ := List.mem_flatMap.mp found
  unfold atomResults at inAtom
  split at inAtom
  · next left right viewed =>
      obtain rfl := eq_equation_of_viewEquation viewed
      obtain ⟨closed, noRun, wasQuoted⟩ := safe left right stored
      split at inAtom
      · next exact =>
          simp only [Bool.and_eq_true] at exact
          obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp inAtom
          have rebuilt : applyBindings bindings (asRule left) = subject :=
            matchPattern_correct matched exact.1
          have leftUses := uses_sealed_of_instance (depth := depth) (bindings := bindings)
            (asRule left) false exact.1 (by rw [rebuilt]; exact kept)
          have values := holds_of_matched (holds := SealedWithPlainRuns depth)
            (fun label arguments both => both.of_mem_apply) (asRule left) exact.1 matched kept
          refine sealedWithPlainRuns_instance (asRule right) false exact.2
            (isWellScopedAt_asRule right 0 closed) (tokens_asRule_eq_zero right noRun) ?_
          rintro ⟨name, beneath⟩ member
          cases beneath with
          | true => exact leftUses (name, true) (wasQuoted name member)
          | false =>
              show SealedWithPlainRuns depth (applyBindings bindings (.fvar name))
              rcases applyBindings_fvar_cases bindings name with ⟨entry, inBindings, same⟩ | same
              · rw [same]
                exact values entry inBindings
              · rw [same]
                exact ⟨by simp [sealedAt, binderSafeAt], by rw [runsPlain]⟩
      · cases inAtom
  · cases inAtom

/-- A count that counts fewer constructors is zero where one that counts more
is. -/
theorem tokens_eq_zero_of_counts_fewer {fewer more : String → Bool}
    (among : ∀ label : String, fewer label = true → more label = true) (pattern : Pattern) :
    tokens more pattern = 0 → tokens fewer pattern = 0 := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments ih =>
      intro zero
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp zero
      refine tokens_apply_eq_zero_iff.mpr
        ⟨?_, fun argument member => ih argument member (each argument member)⟩
      cases counts : fewer label with
      | false => rfl
      | true =>
          rw [among label counts] at uncounted
          cases uncounted
  | hlambda binder body ih =>
      intro zero
      rw [tokens] at zero ⊢
      exact ih zero
  | hmultiLambda arity binders body ih =>
      intro zero
      rw [tokens] at zero ⊢
      exact ih zero
  | hsubst body replacement ihBody ihReplacement =>
      intro zero
      rw [tokens] at zero
      rw [tokens, ihBody (by omega), ihReplacement (by omega)]
  | hcollection kind elements rest ih =>
      intro zero
      rw [tokens] at zero
      rw [tokens]
      exact tokensList_eq_zero fun element member =>
        ih element member (tokens_eq_zero_of_mem zero element member)

/-- In a pattern without quotation no variable is used beneath a quotation,
unless the pattern itself is beneath one. -/
theorem variableUses_of_tokens_eq_zero {counted : String → Bool}
    (quote : counted "prime-quote" = true) (pattern : Pattern) :
    ∀ beneath : Bool, tokens counted pattern = 0 →
      ∀ use ∈ variableUses beneath pattern, use.2 = beneath := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro beneath _ use member; simp [variableUses] at member
  | hfvar name =>
      intro beneath _ use member
      rw [variableUses, List.mem_singleton] at member
      rw [member]
  | happly label arguments ih =>
      intro beneath zero use member
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp zero
      have other : ¬ (label = "prime-quote" ∧ arguments.length = 1) := by
        rintro ⟨rfl, -⟩
        rw [quote] at uncounted
        cases uncounted
      rw [variableUses_apply_of_not_quotation other, mem_variableUsesList] at member
      obtain ⟨argument, inArguments, inner⟩ := member
      exact ih argument inArguments beneath (each argument inArguments) use inner
  | hlambda binder body _ => intro beneath _ use member; simp [variableUses] at member
  | hmultiLambda arity binders body _ => intro beneath _ use member; simp [variableUses] at member
  | hsubst body replacement _ _ => intro beneath _ use member; simp [variableUses] at member
  | hcollection kind elements rest _ =>
      intro beneath _ use member
      simp [variableUses] at member

/-- **Positive**: a plain space quotes only what was quoted; it stores no
quotation. -/
theorem quotesOnlyQuoted_of_plainSpace {space : Pattern} (plain : plainSpace space = true) :
    QuotesOnlyQuoted space := by
  intro left right stored
  obtain ⟨closed, quiet⟩ := plainSpace_iff.mp plain
  have atomClosed : (Pattern.apply "=" [left, right]).isWellScopedAt 0 = true :=
    holds_of_mem_storedAtoms (holds := fun pattern => pattern.isWellScopedAt 0 = true)
      wellScoped_of_mem_apply space closed _ stored
  have atomQuiet : tokens quoteOrRun (.apply "=" [left, right]) = 0 :=
    tokens_of_mem_storedAtoms space quiet _ stored
  have rightQuiet : tokens quoteOrRun right = 0 :=
    (tokens_apply_eq_zero_iff.mp atomQuiet).2 right (by simp)
  refine ⟨wellScoped_of_mem_apply "=" [left, right] atomClosed right (by simp),
    tokens_eq_zero_of_counts_fewer (fewer := runLabel) (more := quoteOrRun)
      (fun label isRun => by simp [runLabel] at isRun; simp [quoteOrRun, isRun]) right rightQuiet,
    fun name member => ?_⟩
  have outside := variableUses_of_tokens_eq_zero (counted := quoteOrRun) (by decide)
    (asRule right) false (tokens_asRule_eq_zero right rightQuiet) (name, true) member
  cases outside

/-- **Positive**: a space that stores an equation whose right side drops the
quotation of a closed atom.  It is not plain (`not_plainSpace_quoting`). -/
theorem quotesOnlyQuoted_closedQuotation :
    QuotesOnlyQuoted (spaceOfAtoms [.apply "=" [unitAtom, dropped (quoted unitAtom)]]) := by
  intro left right stored
  rw [storedAtoms_spaceOfAtoms] at stored
  simp only [List.mem_cons, List.not_mem_nil, or_false, Pattern.apply.injEq, List.cons.injEq,
    and_true, true_and] at stored
  obtain ⟨-, rfl⟩ := stored
  refine ⟨by decide +kernel, by decide +kernel, fun name member => ?_⟩
  have none : variableUses false (asRule (dropped (quoted unitAtom))) = [] := by decide +kernel
  rw [none] at member
  cases member

/-- Reading a dropped quotation as a side of a rule reads what it quotes. -/
theorem asRule_dropQuote (pattern : Pattern) :
    asRule (dropped (quoted pattern)) = dropped (quoted (asRule pattern)) := by
  rw [dropped, asRule_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil]
  rw [quoted, asRule_apply_of_ne (by decide)]
  rfl

/-- The space of the rule `*@$0 ⟶ *@$0`: the dropped quotation of every atom
has itself as an answer. -/
def requotingSpace : Pattern :=
  spaceOfAtoms [.apply "=" [dropped (quoted (variableAtom (numeral 0))),
    dropped (quoted (variableAtom (numeral 0)))]]

/-- **Positive**: the space of the rule `*@$0 ⟶ *@$0`.  Its variable is
beneath a quotation on both sides; it is not plain. -/
theorem quotesOnlyQuoted_requoting :
    QuotesOnlyQuoted requotingSpace ∧ plainSpace requotingSpace = false := by
  refine ⟨?_, by decide +kernel⟩
  intro left right stored
  rw [requotingSpace, storedAtoms_spaceOfAtoms] at stored
  simp only [List.mem_cons, List.not_mem_nil, or_false, Pattern.apply.injEq, List.cons.injEq,
    and_true, true_and] at stored
  obtain ⟨rfl, rfl⟩ := stored
  exact ⟨by decide +kernel, by decide +kernel, fun name member => member⟩

/-- **Negative**: the space of the rule `$0 ⟶ *@$0`.  Its variable is beneath
a quotation on the right, and outside every quotation on the left. -/
theorem not_quotesOnlyQuoted_quotingSpace : ¬ QuotesOnlyQuoted quotingSpace := by
  intro safe
  have stored : Pattern.apply "=" [variableAtom (numeral 0),
      dropped (quoted (variableAtom (numeral 0)))] ∈ storedAtoms quotingSpace := by
    rw [quotingSpace, storedAtoms_spaceOfAtoms]
    exact List.mem_singleton.mpr rfl
  have onLeft := (safe _ _ stored).2.2 (metaName 0) (by
    rw [asRule_dropQuote, asRule_variableAtom, dropped, variableUses_apply_of_not_quotation
      (by decide), variableUsesList, variableUsesList, quoted, variableUses_quotation,
      variableUses]
    exact List.mem_append_left _ (List.mem_singleton.mpr rfl))
  rw [asRule_variableAtom, variableUses, List.mem_singleton] at onLeft
  cases (Prod.mk.inj onLeft).2

/-! ## A step keeps a pattern sealed -/

/-- **A step of the candidate, at an ambient space whose contraction quotes
only what was quoted, keeps a pattern sealed with plain runs**, under every
guard and beneath every number of binders. -/
theorem spacesAndRegions_step_sealed {admits : Pattern → Bool} {ambientSpace : Pattern}
    (safe : QuotesOnlyQuoted (contract ambientSpace)) {depth : Nat} {source target : Pattern}
    (moved : Step (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (kept : SealedWithPlainRuns depth source) : SealedWithPlainRuns depth target := by
  obtain ⟨fuel, bounded⟩ := moved
  exact sealedWithPlainRuns_invariant.stepAt spacesAndRegions_rewrites
    (fun subjectKept found => safe.sealed_of_mem_matchResults subjectKept.contract found)
    fuel bounded kept

/-- **And it keeps a pattern sealed with plain runs up to the static
equivalence**: the contraction of what it reaches is sealed with plain runs
when the contraction of where it starts is. -/
theorem spacesAndRegions_step_sealedUpToStatics {admits : Pattern → Bool} {ambientSpace : Pattern}
    (safe : QuotesOnlyQuoted (contract ambientSpace)) {depth : Nat} {source target : Pattern}
    (moved : Step (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (kept : SealedWithPlainRuns depth (contract source)) :
    SealedWithPlainRuns depth (contract target) := by
  obtain ⟨fuel, bounded⟩ := moved
  exact sealedUpToStatics_invariant.stepAt spacesAndRegions_rewrites
    (fun subjectKept found => (safe.sealed_of_mem_matchResults subjectKept found).contract)
    fuel bounded kept

/-! ## The condition on the spaces of runs is needed -/

/-- An abstraction whose body runs, in the space of the rule `$0 ⟶ *@$0`, an
atom that mentions the bound variable: `λ x. run(S, (() x))`. -/
def runsMention : Pattern :=
  .apply "Lam" [unitAtom,
    .lambda none (runPattern quotingSpace (.apply "App" [unitAtom, .bvar 0]))]

/-- The abstraction whose run holds the dropped quotation of that atom:
`λ x. run(S, *@(() x))`. -/
def runsQuotation : Pattern :=
  .apply "Lam" [unitAtom,
    .lambda none (runPattern quotingSpace (dropped (quoted (.apply "App" [unitAtom, .bvar 0]))))]

/-- **At the empty ambient space an abstraction that is sealed, with a run in
the space of the rule `$0 ⟶ *@$0`, steps to one that is not sealed.**  The
ambient space stores nothing; the step is the root step of the run, in its
own space.  So sealing alone is not kept, and the runs of a sealed pattern
are asked to have plain spaces. -/
theorem quotingRun_unseals :
    sealedAt 0 runsMention = true ∧ runsPlain runsMention = false ∧
      Step (regionEvaluator anySubject emptySpace) spacesAndRegions runsMention runsQuotation ∧
        sealedAt 0 runsQuotation = false := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  have inner : Step (regionEvaluator anySubject quotingSpace) spacesAndRegions
      (.apply "App" [unitAtom, .bvar 0])
      (dropped (quoted (.apply "App" [unitAtom, .bvar 0]))) :=
    assembledOver_root_step (admits := anySubject) allHeaded.name
      (constructors := atomsReduce.terms) (constructor := applicationConstructor) (by decide)
      (by decide) (arguments := [unitAtom, .bvar 0]) (by decide)
      (quotingSpace_answers (subject := .apply "App" [unitAtom, .bvar 0]) (by decide +kernel))
  obtain ⟨fuel, moved⟩ := (spacesAndRegions_run_step_iff (admits := anySubject)
    (ambientSpace := emptySpace)).mpr ⟨_, rfl, inner⟩
  exact ⟨fuel + 1, step_lamBody
    (by rw [show spacesAndRegions.rewrites = allHeaded.rewrites from spacesAndRegions_rewrites]
        exact allHeaded_mem_plain (by simp)) unitAtom none moved⟩

#print axioms uses_sealed_of_instance
#print axioms sealedWithPlainRuns_instance
#print axioms QuotesOnlyQuoted.sealed_of_mem_matchResults
#print axioms quotesOnlyQuoted_of_plainSpace
#print axioms quotesOnlyQuoted_closedQuotation
#print axioms quotesOnlyQuoted_requoting
#print axioms not_quotesOnlyQuoted_quotingSpace
#print axioms spacesAndRegions_step_sealed
#print axioms spacesAndRegions_step_sealedUpToStatics
#print axioms quotingRun_unseals

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
