import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Candidate
import Mettapedia.Logic.HostingStyles.AmbientSpace.Tokens
import Mettapedia.OSLF.MeTTaIL.QuoteSafeOpening

/-!
# Sealed quotation and plain spaces, on patterns

A pattern is **sealed** beneath `depth` binders when every bound variable in
it is one of those binders or of a binder inside it, and the atom of every
quotation in it is closed: a quotation mentions none of the binders around
it.  That is the quote-aware scope check of the pattern syntax,
`binderSafeAt`, at the quotation constructor of the candidate; it is used
here under the name `sealedAt`, and the lemmas of that check about lifting
and about the instantiation of a binder are lemmas of it.

A run carries a space, and a step beneath a run asks that space.  So an
invariant of the steps of the candidate has to say something of the spaces
of the runs in a pattern.

* `plainSpace space`: the space is closed and contains no quotation and no
  run.  The space of a table of rules is plain (`plainSpace_ruleSpace`); a
  space that stores a quotation is not (`not_plainSpace_quoting`).
* `runsPlain pattern`: every run in the pattern has a plain space.
* `SealedWithPlainRuns depth pattern`: both.

This module proves what the operations out of which a step is made do to the
three:

* **the constructors**: an application of a constructor other than quotation
  is sealed exactly when its arguments are (`sealedAt_apply_of_ne`), a
  quotation exactly when its atom is closed and sealed (`sealedAt_quoted`),
  a run exactly when its space and its subject are;
* **lifting and instantiation** keep `runsPlain`
  (`runsPlain_liftBVars`, `runsPlain_instantiateBVarAt`), as they keep
  `sealedAt`;
* **contraction** keeps both (`sealedAt_contract`, `runsPlain_contract`),
  fixes a pattern without quotation (`contract_of_tokens_eq_zero`), and
  commutes with lifting and with instantiation up to itself
  (`contract_liftBVars_contract`, `contract_instantiateBVarAt_contract`).

**In a sealed pattern the instantiation of a binder changes no quotation.**
A quotation in a sealed pattern is fixed by the instantiation
(`instantiateBVarAt_quoted_of_sealed`), every quotation of a sealed body is a
quotation of its instance (`quotations_subset_instantiateBVarAt`), and every
quotation of the instance is a quotation of the body or of the argument
(`quotations_instantiateBVarAt_subset`).  Negative: the body of the
abstraction that drops a quotation of its bound variable is not sealed, and
its quotation is not a quotation of its instance
(`quotation_changed_when_not_sealed`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution
  (liftBVars liftBVarsList liftBVarsList_eq_map instantiateBVarAt instantiateBVar
    liftBVars_eq_self_of_isWellScopedAt instantiateBVarAt_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
  (contract contractList contractRoot contractList_eq_map contractRoot_of_ne contract_apply_of_ne
    contractRoot_quote_cases quoted dropped runPattern unitAtom numeral emptySpace addAtom
    spaceOfAtoms storedAtoms variableAtom)
open Mettapedia.Logic.HostingStyles.AtomsReduce (symbolAtom ruleSpace tokens_ruleSpace)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (tokens_apply_eq_zero_iff tokens_eq_zero_of_mem ruleSpace_wellSorted_of)
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList tokensList_eq_zero)

/-! ## Sealed beneath binders -/

/-- **Sealed beneath `depth` binders**: every bound variable of the pattern
is one of the `depth` binders around it or of a binder inside it, and the
atom of every quotation is closed.  It is the quote-aware scope check of the
pattern syntax at the quotation constructor of the candidate. -/
abbrev sealedAt (depth : Nat) (pattern : Pattern) : Bool :=
  binderSafeAt "prime-quote" depth pattern

/-- **Positive**: an abstraction whose body drops a quotation of a closed
atom. -/
theorem sealedAt_closedQuotation :
    sealedAt 0 (.apply "Lam" [unitAtom, .lambda none (dropped (quoted unitAtom))]) = true := by
  decide +kernel

/-- **Negative**: an abstraction whose body drops a quotation of its bound
variable. -/
theorem not_sealedAt_capturing :
    sealedAt 0 (.apply "Lam" [unitAtom, .lambda none (dropped (quoted (.bvar 0)))]) = false := by
  decide +kernel

/-- **A quotation is sealed exactly when its atom is closed and sealed**,
beneath any number of binders. -/
theorem sealedAt_quoted (depth : Nat) (atom : Pattern) :
    sealedAt depth (quoted atom) = sealedAt 0 atom := by
  simp [sealedAt, quoted, binderSafeAt]

/-- **An application of a constructor other than quotation is sealed exactly
when its arguments are.** -/
theorem sealedAt_apply_of_ne {label : String} (other : label ≠ "prime-quote") (depth : Nat)
    (arguments : List Pattern) :
    sealedAt depth (.apply label arguments) = true ↔
      ∀ argument ∈ arguments, sealedAt depth argument = true := by
  rw [← binderSafeListAt_eq_true_iff]
  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · simp [sealedAt, binderSafeAt, binderSafeListAt]
  · simp [sealedAt, binderSafeAt, other, binderSafeListAt]
  · exact Iff.rfl

/-- An abstraction of the pattern syntax is sealed exactly when its body is,
beneath one more binder. -/
theorem sealedAt_lambda (depth : Nat) (binder : Option String) (body : Pattern) :
    sealedAt depth (.lambda binder body) = sealedAt (depth + 1) body := by
  simp [sealedAt, binderSafeAt]

/-- **The arguments of a sealed application are sealed**, whatever its
constructor: the atom of a quotation is sealed beneath no binder, hence
beneath any. -/
theorem sealedAt_of_mem_apply {label : String} {arguments : List Pattern} {depth : Nat}
    (safe : sealedAt depth (.apply label arguments) = true) :
    ∀ argument ∈ arguments, sealedAt depth argument = true := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rcases arguments with _ | ⟨atom, _ | ⟨second, rest⟩⟩
    · intro argument member
      cases member
    · intro argument member
      rw [List.mem_singleton.mp member]
      have inner : sealedAt 0 atom = true := by simpa [sealedAt, binderSafeAt] using safe
      exact binderSafeAt_mono "prime-quote" inner (Nat.zero_le depth)
    · exact (binderSafeListAt_eq_true_iff "prime-quote" depth (atom :: second :: rest)).mp safe
  · exact (sealedAt_apply_of_ne isQuote depth arguments).mp safe

/-- **A change of the arguments of a sealed application that keeps each of
them sealed, beneath every number of binders, keeps the application
sealed.** -/
theorem sealedAt_apply_map {label : String} {arguments : List Pattern}
    {change : Pattern → Pattern}
    (keeps : ∀ argument ∈ arguments, ∀ depth : Nat, sealedAt depth argument = true →
      sealedAt depth (change argument) = true)
    {depth : Nat} (safe : sealedAt depth (.apply label arguments) = true) :
    sealedAt depth (.apply label (arguments.map change)) = true := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rcases arguments with _ | ⟨atom, _ | ⟨second, rest⟩⟩
    · exact safe
    · have inner : sealedAt 0 atom = true := by simpa [sealedAt, binderSafeAt] using safe
      simpa [sealedAt, binderSafeAt] using keeps atom (by simp) 0 inner
    · have each :=
        (binderSafeListAt_eq_true_iff "prime-quote" depth (atom :: second :: rest)).mp safe
      show binderSafeListAt "prime-quote" depth ((atom :: second :: rest).map change) = true
      rw [binderSafeListAt_eq_true_iff]
      intro changed member
      obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
      exact keeps argument inArguments depth (each argument inArguments)
  · rw [sealedAt_apply_of_ne isQuote] at safe ⊢
    intro changed member
    obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
    exact keeps argument inArguments depth (safe argument inArguments)

/-- **A pattern that is closed beneath `depth` binders and has no quotation
is sealed there.** -/
theorem sealedAt_of_wellScoped {counted : String → Bool} (quote : counted "prime-quote" = true)
    (pattern : Pattern) :
    ∀ depth : Nat, pattern.isWellScopedAt depth = true → tokens counted pattern = 0 →
      sealedAt depth pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth closed _
      simpa [sealedAt, binderSafeAt, Pattern.isWellScopedAt] using closed
  | hfvar name =>
      intro depth _ _
      simp [sealedAt, binderSafeAt]
  | happly label arguments ih =>
      intro depth closed zero
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      have other : label ≠ "prime-quote" := by
        rintro rfl
        rw [quote] at uncounted
        cases uncounted
      have closedEach : ∀ argument ∈ arguments, argument.isWellScopedAt depth = true := by
        simp only [Pattern.isWellScopedAt] at closed
        exact (isWellScopedListAt_eq_true_iff depth arguments).mp closed
      exact (sealedAt_apply_of_ne other depth arguments).mpr fun argument member =>
        ih argument member depth (closedEach argument member) (clean argument member)
  | hlambda binder body ih =>
      intro depth closed zero
      simp only [Pattern.isWellScopedAt] at closed
      rw [tokens] at zero
      rw [sealedAt_lambda]
      exact ih (depth + 1) closed zero
  | hmultiLambda arity binders body ih =>
      intro depth closed zero
      simp only [Pattern.isWellScopedAt] at closed
      rw [tokens] at zero
      simpa [sealedAt, binderSafeAt] using ih (depth + arity) closed zero
  | hsubst body replacement ihBody ihReplacement =>
      intro depth closed zero
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at closed
      rw [tokens] at zero
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true]
      exact ⟨ihBody (depth + 1) closed.1 (by omega), ihReplacement depth closed.2 (by omega)⟩
  | hcollection kind elements rest ih =>
      intro depth closed zero
      simp only [Pattern.isWellScopedAt] at closed
      rw [tokens] at zero
      simp only [sealedAt, binderSafeAt]
      rw [binderSafeListAt_eq_true_iff]
      exact fun element member => ih element member depth
        ((isWellScopedListAt_eq_true_iff depth elements).mp closed element member)
        (tokens_eq_zero_of_mem zero element member)

/-! ## Plain spaces -/

/-- Quotation and the run: the two constructors that a plain space does not
contain. -/
def quoteOrRun (label : String) : Bool := label == "prime-quote" || label == "prime-run"

/-- **Positive**: the run. -/
theorem quoteOrRun_run : quoteOrRun "prime-run" = true := by decide

/-- **Negative**: dropping. -/
theorem not_quoteOrRun_drop : quoteOrRun "prime-drop" = false := by decide

/-- **A plain space**: closed, and with no quotation and no run in the atoms
it stores. -/
def plainSpace (space : Pattern) : Bool :=
  space.isWellScopedAt 0 && tokens quoteOrRun space == 0

theorem plainSpace_iff {space : Pattern} :
    plainSpace space = true ↔ space.isWellScopedAt 0 = true ∧ tokens quoteOrRun space = 0 := by
  simp [plainSpace]

/-- **Positive**: the space of a list of rules. -/
theorem plainSpace_ruleSpace (rules : List Dedukti.RewriteRule) :
    plainSpace (ruleSpace rules) = true :=
  plainSpace_iff.mpr ⟨(ruleSpace_wellSorted_of spacesAndRegions_carriesAtoms rules).2.2.2,
    tokens_ruleSpace (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) rules⟩

/-- **Positive**: the empty space. -/
theorem plainSpace_emptySpace : plainSpace emptySpace = true := by decide +kernel

/-- **Negative**: a space that stores an equation whose right side drops a
quotation. -/
theorem not_plainSpace_quoting :
    plainSpace (spaceOfAtoms [.apply "=" [unitAtom, dropped (quoted unitAtom)]]) = false := by
  decide +kernel

/-- **Negative**: a space that mentions a variable bound outside it. -/
theorem not_plainSpace_open : plainSpace (addAtom (.bvar 0) emptySpace) = false := by
  decide +kernel

/-- A plain space is sealed beneath any number of binders. -/
theorem sealedAt_of_plainSpace {space : Pattern} (plain : plainSpace space = true) (depth : Nat) :
    sealedAt depth space = true := by
  obtain ⟨closed, quiet⟩ := plainSpace_iff.mp plain
  exact sealedAt_of_wellScoped (counted := quoteOrRun) (by decide) space depth
    (isWellScopedAt_mono closed (Nat.zero_le depth)) quiet

/-! ## Every run has a plain space -/

/-- Whether the first of a list of patterns, when there is one, is a plain
space: the first argument of a run is its space. -/
def headPlain : List Pattern → Bool
  | [] => true
  | space :: _ => plainSpace space

/-- **Positive**: a list that begins with the empty space. -/
theorem headPlain_emptySpace : headPlain [emptySpace, unitAtom] = true := by decide +kernel

/-- **Negative**: a list that begins with a space that mentions a variable
bound outside it. -/
theorem not_headPlain_open : headPlain [addAtom (.bvar 0) emptySpace, unitAtom] = false := by
  decide +kernel

mutual
  /-- **Every run in the pattern has a plain space.** -/
  def runsPlain : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply label arguments =>
        (label != "prime-run" || headPlain arguments) && runsPlainList arguments
    | .lambda _ body => runsPlain body
    | .multiLambda _ _ body => runsPlain body
    | .subst body replacement => runsPlain body && runsPlain replacement
    | .collection _ elements _ => runsPlainList elements

  /-- Every run in the patterns of a list has a plain space. -/
  def runsPlainList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => runsPlain pattern && runsPlainList patterns
end

/-- **Positive**: a run in the empty space, beneath a quotation. -/
theorem runsPlain_quotedRun :
    runsPlain (dropped (quoted (runPattern emptySpace unitAtom))) = true := by decide +kernel

/-- **Negative**: a run in a space that mentions a variable bound outside
it. -/
theorem not_runsPlain_openSpace :
    runsPlain (.apply "Lam" [unitAtom,
      .lambda none (runPattern (addAtom (.bvar 0) emptySpace) unitAtom)]) = false := by
  decide +kernel

theorem runsPlainList_eq_true_iff (patterns : List Pattern) :
    runsPlainList patterns = true ↔ ∀ pattern ∈ patterns, runsPlain pattern = true := by
  induction patterns with
  | nil => simp [runsPlainList]
  | cons pattern patterns ih => simp [runsPlainList, ih]

/-- **The runs of an application**: its own space, when it is a run, and the
runs of its arguments. -/
theorem runsPlain_apply (label : String) (arguments : List Pattern) :
    runsPlain (.apply label arguments) = true ↔
      (label = "prime-run" → headPlain arguments = true) ∧
        ∀ argument ∈ arguments, runsPlain argument = true := by
  rw [runsPlain, ← runsPlainList_eq_true_iff]
  by_cases isRun : label = "prime-run" <;> simp [isRun]

/-- The runs of an application of a constructor other than the run are those
of its arguments. -/
theorem runsPlain_apply_of_ne {label : String} (other : label ≠ "prime-run")
    (arguments : List Pattern) :
    runsPlain (.apply label arguments) = true ↔
      ∀ argument ∈ arguments, runsPlain argument = true := by
  rw [runsPlain_apply]
  exact ⟨fun both => both.2, fun each => ⟨fun isRun => absurd isRun other, each⟩⟩

/-- **The runs of a run**: its space is plain, and the runs of its space and
of its subject have plain spaces. -/
theorem runsPlain_runPattern (space subject : Pattern) :
    runsPlain (runPattern space subject) = true ↔
      plainSpace space = true ∧ runsPlain space = true ∧ runsPlain subject = true := by
  rw [runPattern, runsPlain_apply]
  simp [headPlain]

/-- **A pattern with no run has no run in a space that is not plain**, for
every count that counts the run. -/
theorem runsPlain_of_tokens_eq_zero {counted : String → Bool} (run : counted "prime-run" = true)
    (pattern : Pattern) : tokens counted pattern = 0 → runsPlain pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [runsPlain]
  | hfvar name => intro _; rw [runsPlain]
  | happly label arguments ih =>
      intro zero
      obtain ⟨uncounted, each⟩ := tokens_apply_eq_zero_iff.mp zero
      have other : label ≠ "prime-run" := by
        rintro rfl
        rw [run] at uncounted
        cases uncounted
      exact (runsPlain_apply_of_ne other arguments).mpr fun argument member =>
        ih argument member (each argument member)
  | hlambda binder body ih =>
      intro zero
      rw [tokens] at zero
      rw [runsPlain]
      exact ih zero
  | hmultiLambda arity binders body ih =>
      intro zero
      rw [tokens] at zero
      rw [runsPlain]
      exact ih zero
  | hsubst body replacement ihBody ihReplacement =>
      intro zero
      rw [tokens] at zero
      rw [runsPlain, ihBody (by omega), ihReplacement (by omega)]
      rfl
  | hcollection kind elements rest ih =>
      intro zero
      rw [tokens] at zero
      rw [runsPlain, runsPlainList_eq_true_iff]
      exact fun element member => ih element member (tokens_eq_zero_of_mem zero element member)

/-- A plain space has no run in a space that is not plain: it has no run. -/
theorem runsPlain_of_plainSpace {space : Pattern} (plain : plainSpace space = true) :
    runsPlain space = true :=
  runsPlain_of_tokens_eq_zero (counted := quoteOrRun) (by decide) space (plainSpace_iff.mp plain).2

/-- A change of patterns that fixes every plain space keeps the first of a
list a plain space. -/
theorem headPlain_map {change : Pattern → Pattern}
    (fixes : ∀ space : Pattern, plainSpace space = true → change space = space) :
    ∀ {arguments : List Pattern}, headPlain arguments = true →
      headPlain (arguments.map change) = true
  | [], _ => rfl
  | space :: _, plain => by
      rw [List.map_cons, headPlain, fixes space plain]
      exact plain

/-- **Lifting keeps the spaces of the runs plain**: a plain space is closed,
so lifting does not change it. -/
theorem runsPlain_liftBVars (pattern : Pattern) :
    ∀ cutoff shift : Nat, runsPlain pattern = true →
      runsPlain (liftBVars cutoff shift pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff shift _
      rw [liftBVars]
      split <;> rw [runsPlain]
  | hfvar name =>
      intro cutoff shift _
      rw [liftBVars, runsPlain]
  | happly label arguments ih =>
      intro cutoff shift plain
      obtain ⟨head, each⟩ := (runsPlain_apply label arguments).mp plain
      rw [liftBVars, liftBVarsList_eq_map]
      refine (runsPlain_apply label _).mpr ⟨fun isRun => ?_, fun lifted member => ?_⟩
      · exact headPlain_map (fun space plainOne => liftBVars_eq_self_of_isWellScopedAt
          (isWellScopedAt_mono (plainSpace_iff.mp plainOne).1 (Nat.zero_le cutoff))) (head isRun)
      · obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments cutoff shift (each argument inArguments)
  | hlambda binder body ih =>
      intro cutoff shift plain
      rw [runsPlain] at plain
      rw [liftBVars, runsPlain]
      exact ih _ _ plain
  | hmultiLambda arity binders body ih =>
      intro cutoff shift plain
      rw [runsPlain] at plain
      rw [liftBVars, runsPlain]
      exact ih _ _ plain
  | hsubst body replacement ihBody ihReplacement =>
      intro cutoff shift plain
      rw [runsPlain, Bool.and_eq_true] at plain
      rw [liftBVars, runsPlain, Bool.and_eq_true]
      exact ⟨ihBody _ _ plain.1, ihReplacement _ _ plain.2⟩
  | hcollection kind elements rest ih =>
      intro cutoff shift plain
      rw [runsPlain, runsPlainList_eq_true_iff] at plain
      rw [liftBVars, liftBVarsList_eq_map, runsPlain, runsPlainList_eq_true_iff]
      intro lifted member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
      exact ih element inElements cutoff shift (plain element inElements)

/-- **The instantiation of a binder keeps the spaces of the runs plain**,
when those of the argument are: a plain space is closed, so the
instantiation does not change it. -/
theorem runsPlain_instantiateBVarAt {replacement : Pattern}
    (plainReplacement : runsPlain replacement = true) (pattern : Pattern) :
    ∀ depth : Nat, runsPlain pattern = true →
      runsPlain (instantiateBVarAt depth replacement pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth _
      rw [instantiateBVarAt]
      split
      · rw [runsPlain]
      · split
        · exact runsPlain_liftBVars replacement 0 depth plainReplacement
        · rw [runsPlain]
  | hfvar name =>
      intro depth _
      rw [instantiateBVarAt, runsPlain]
  | happly label arguments ih =>
      intro depth plain
      obtain ⟨head, each⟩ := (runsPlain_apply label arguments).mp plain
      rw [instantiateBVarAt]
      refine (runsPlain_apply label _).mpr ⟨fun isRun => ?_, fun instantiated member => ?_⟩
      · exact headPlain_map (fun space plainOne => instantiateBVarAt_eq_self_of_isWellScopedAt
          (isWellScopedAt_mono (plainSpace_iff.mp plainOne).1 (Nat.zero_le depth))) (head isRun)
      · obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
        exact ih argument inArguments depth (each argument inArguments)
  | hlambda binder body ih =>
      intro depth plain
      rw [runsPlain] at plain
      rw [instantiateBVarAt, runsPlain]
      exact ih _ plain
  | hmultiLambda arity binders body ih =>
      intro depth plain
      rw [runsPlain] at plain
      rw [instantiateBVarAt, runsPlain]
      exact ih _ plain
  | hsubst body nested ihBody ihNested =>
      intro depth plain
      rw [runsPlain, Bool.and_eq_true] at plain
      rw [instantiateBVarAt, runsPlain, Bool.and_eq_true]
      exact ⟨ihBody _ plain.1, ihNested _ plain.2⟩
  | hcollection kind elements rest ih =>
      intro depth plain
      rw [runsPlain, runsPlainList_eq_true_iff] at plain
      rw [instantiateBVarAt, runsPlain, runsPlainList_eq_true_iff]
      intro instantiated member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
      exact ih element inElements depth (plain element inElements)

/-! ## Sealed, with plain runs -/

/-- **Sealed beneath `depth` binders, and every run in a plain space.** -/
def SealedWithPlainRuns (depth : Nat) (pattern : Pattern) : Prop :=
  sealedAt depth pattern = true ∧ runsPlain pattern = true

/-- **Positive**: a run in the empty space beneath a quotation, beneath a
binder. -/
theorem sealedWithPlainRuns_quotedRun :
    SealedWithPlainRuns 0 (.apply "Lam" [unitAtom,
      .lambda none (dropped (quoted (runPattern emptySpace unitAtom)))]) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Negative**: a quotation of the bound variable of the abstraction
around it. -/
theorem not_sealedWithPlainRuns_capturing :
    ¬ SealedWithPlainRuns 0 (.apply "Lam" [unitAtom, .lambda none (dropped (quoted (.bvar 0)))]) :=
  fun both => absurd both.1 (by decide +kernel)

/-- The arguments of an application that is sealed with plain runs are. -/
theorem SealedWithPlainRuns.of_mem_apply {label : String} {arguments : List Pattern}
    {depth : Nat} (kept : SealedWithPlainRuns depth (.apply label arguments)) :
    ∀ argument ∈ arguments, SealedWithPlainRuns depth argument :=
  fun argument member => ⟨sealedAt_of_mem_apply kept.1 argument member,
    ((runsPlain_apply label arguments).mp kept.2).2 argument member⟩

/-- **An application of a constructor other than quotation and the run is
sealed with plain runs exactly when its arguments are.** -/
theorem sealedWithPlainRuns_apply_iff {label : String} (other : quoteOrRun label = false)
    (depth : Nat) (arguments : List Pattern) :
    SealedWithPlainRuns depth (.apply label arguments) ↔
      ∀ argument ∈ arguments, SealedWithPlainRuns depth argument := by
  have notQuote : label ≠ "prime-quote" := by
    rintro rfl
    exact absurd other (by decide)
  have notRun : label ≠ "prime-run" := by
    rintro rfl
    exact absurd other (by decide)
  unfold SealedWithPlainRuns
  rw [sealedAt_apply_of_ne notQuote, runsPlain_apply_of_ne notRun]
  exact ⟨fun both argument member => ⟨both.1 argument member, both.2 argument member⟩,
    fun each => ⟨fun argument member => (each argument member).1,
      fun argument member => (each argument member).2⟩⟩

/-- **A run is sealed with plain runs exactly when its space is plain and its
subject is sealed with plain runs.** -/
theorem sealedWithPlainRuns_runPattern (depth : Nat) (space subject : Pattern) :
    SealedWithPlainRuns depth (runPattern space subject) ↔
      plainSpace space = true ∧ SealedWithPlainRuns depth subject := by
  unfold SealedWithPlainRuns
  rw [runPattern, sealedAt_apply_of_ne (by decide), ← runPattern, runsPlain_runPattern]
  constructor
  · rintro ⟨each, plain, -, subjectPlain⟩
    exact ⟨plain, each subject (by simp), subjectPlain⟩
  · rintro ⟨plain, subjectSealed, subjectPlain⟩
    refine ⟨fun argument member => ?_, plain, runsPlain_of_plainSpace plain, subjectPlain⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact sealedAt_of_plainSpace plain depth
    · exact subjectSealed

/-! ## Contraction -/

/-- The contraction of an application: the contraction at its root of the
contractions of its arguments. -/
theorem contract_apply (label : String) (arguments : List Pattern) :
    contract (.apply label arguments) = contractRoot label (arguments.map contract) := by
  rw [contract, contractList_eq_map]

/-- **What the contraction at a root does**: it returns what was dropped,
when the root is a quotation of one dropping, and the application as it is
written otherwise. -/
theorem contractRoot_cases (label : String) (arguments : List Pattern) :
    (∃ name, label = "prime-quote" ∧ arguments = [.apply "prime-drop" [name]] ∧
        contractRoot label arguments = name) ∨
      contractRoot label arguments = .apply label arguments := by
  by_cases isQuote : label = "prime-quote"
  · subst isQuote
    rcases arguments with _ | ⟨head, _ | ⟨second, rest⟩⟩
    · exact .inr (by simp [contractRoot])
    · rcases contractRoot_quote_cases head with ⟨name, rfl, value⟩ | plain
      · exact .inl ⟨name, rfl, rfl, value⟩
      · exact .inr plain
    · exact .inr (by simp [contractRoot])
  · exact .inr (contractRoot_of_ne isQuote arguments)

/-- **Contraction keeps a pattern sealed.**  Where it removes a quotation of
a dropping, what was dropped stood beneath the quotation, so it is closed. -/
theorem sealedAt_contract (pattern : Pattern) :
    ∀ depth : Nat, sealedAt depth pattern = true → sealedAt depth (contract pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth safe; rw [contract]; exact safe
  | hfvar name => intro depth safe; rw [contract]; exact safe
  | happly label arguments ih =>
      intro depth safe
      have mapped : sealedAt depth (.apply label (arguments.map contract)) = true :=
        sealedAt_apply_map (fun argument member => ih argument member) safe
      rw [contract_apply]
      rcases contractRoot_cases label (arguments.map contract) with
        ⟨name, rfl, shape, value⟩ | plain
      · rw [value]
        rw [shape] at mapped
        have beneath : sealedAt 0 (.apply "prime-drop" [name]) = true := by
          simpa [sealedAt, binderSafeAt] using mapped
        exact binderSafeAt_mono "prime-quote"
          ((sealedAt_apply_of_ne (by decide) 0 [name]).mp beneath name (by simp))
          (Nat.zero_le depth)
      · rw [plain]
        exact mapped
  | hlambda binder body ih =>
      intro depth safe
      rw [sealedAt_lambda] at safe
      rw [contract, sealedAt_lambda]
      exact ih _ safe
  | hmultiLambda arity binders body ih =>
      intro depth safe
      have inner : sealedAt (depth + arity) body = true := by
        simpa [sealedAt, binderSafeAt] using safe
      rw [contract]
      simpa [sealedAt, binderSafeAt] using ih _ inner
  | hsubst body replacement ihBody ihReplacement =>
      intro depth safe
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true] at safe
      rw [contract]
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true]
      exact ⟨ihBody _ safe.1, ihReplacement _ safe.2⟩
  | hcollection kind elements rest ih =>
      intro depth safe
      simp only [sealedAt, binderSafeAt] at safe
      rw [binderSafeListAt_eq_true_iff] at safe
      rw [contract, contractList_eq_map]
      simp only [sealedAt, binderSafeAt]
      rw [binderSafeListAt_eq_true_iff]
      intro contracted member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
      exact ih element inElements depth (safe element inElements)

/-- **Contraction fixes a pattern without quotation.** -/
theorem contract_of_tokens_eq_zero {counted : String → Bool}
    (quote : counted "prime-quote" = true) (pattern : Pattern) :
    tokens counted pattern = 0 → contract pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rw [contract]
  | hfvar name => intro _; rw [contract]
  | happly label arguments ih =>
      intro zero
      obtain ⟨uncounted, clean⟩ := tokens_apply_eq_zero_iff.mp zero
      have other : label ≠ "prime-quote" := by
        rintro rfl
        rw [quote] at uncounted
        cases uncounted
      rw [contract_apply_of_ne other]
      congr 1
      exact (List.map_congr_left fun argument member =>
        (ih argument member (clean argument member) : contract argument = id argument)).trans
        (List.map_id arguments)
  | hlambda binder body ih =>
      intro zero
      rw [tokens] at zero
      rw [contract, ih zero]
  | hmultiLambda arity binders body ih =>
      intro zero
      rw [tokens] at zero
      rw [contract, ih zero]
  | hsubst body replacement ihBody ihReplacement =>
      intro zero
      rw [tokens] at zero
      rw [contract, ihBody (by omega), ihReplacement (by omega)]
  | hcollection kind elements rest ih =>
      intro zero
      rw [tokens] at zero
      rw [contract, contractList_eq_map]
      congr 1
      exact (List.map_congr_left fun element member =>
        (ih element member (tokens_eq_zero_of_mem zero element member) :
          contract element = id element)).trans (List.map_id elements)

/-- Contraction fixes a plain space. -/
theorem contract_of_plainSpace {space : Pattern} (plain : plainSpace space = true) :
    contract space = space :=
  contract_of_tokens_eq_zero (counted := quoteOrRun) (by decide) space (plainSpace_iff.mp plain).2

/-- **Contraction keeps the spaces of the runs plain.** -/
theorem runsPlain_contract (pattern : Pattern) :
    runsPlain pattern = true → runsPlain (contract pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro plain; rw [contract]; exact plain
  | hfvar name => intro plain; rw [contract]; exact plain
  | happly label arguments ih =>
      intro plain
      obtain ⟨head, each⟩ := (runsPlain_apply label arguments).mp plain
      have mapped : runsPlain (.apply label (arguments.map contract)) = true :=
        (runsPlain_apply label _).mpr ⟨fun isRun =>
            headPlain_map (fun space plainOne => contract_of_plainSpace plainOne) (head isRun),
          fun contracted member => by
            obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp member
            exact ih argument inArguments (each argument inArguments)⟩
      rw [contract_apply]
      rcases contractRoot_cases label (arguments.map contract) with
        ⟨name, rfl, shape, value⟩ | same
      · rw [value]
        rw [shape] at mapped
        have dropping := ((runsPlain_apply "prime-quote" _).mp mapped).2
          (.apply "prime-drop" [name]) (by simp)
        exact ((runsPlain_apply "prime-drop" _).mp dropping).2 name (by simp)
      · rw [same]
        exact mapped
  | hlambda binder body ih =>
      intro plain
      rw [runsPlain] at plain
      rw [contract, runsPlain]
      exact ih plain
  | hmultiLambda arity binders body ih =>
      intro plain
      rw [runsPlain] at plain
      rw [contract, runsPlain]
      exact ih plain
  | hsubst body replacement ihBody ihReplacement =>
      intro plain
      rw [runsPlain, Bool.and_eq_true] at plain
      rw [contract, runsPlain, Bool.and_eq_true]
      exact ⟨ihBody plain.1, ihReplacement plain.2⟩
  | hcollection kind elements rest ih =>
      intro plain
      rw [runsPlain, runsPlainList_eq_true_iff] at plain
      rw [contract, contractList_eq_map, runsPlain, runsPlainList_eq_true_iff]
      intro contracted member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
      exact ih element inElements (plain element inElements)

/-- **Contraction keeps a pattern sealed with plain runs.** -/
theorem SealedWithPlainRuns.contract {depth : Nat} {pattern : Pattern}
    (kept : SealedWithPlainRuns depth pattern) :
    SealedWithPlainRuns depth (Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles.contract pattern) :=
  ⟨sealedAt_contract pattern depth kept.1, runsPlain_contract pattern kept.2⟩

/-- **The contraction at a root, through a change of patterns that goes
beneath every constructor**: contracting the changed arguments and then at
the root is contracting the change of the contraction at the root. -/
theorem contractRoot_map_change {change : Pattern → Pattern}
    (structural : ∀ (label : String) (arguments : List Pattern),
      change (.apply label arguments) = .apply label (arguments.map change))
    (label : String) (contracted : List Pattern) :
    contractRoot label (contracted.map fun part => contract (change part)) =
      contract (change (contractRoot label contracted)) := by
  rcases contractRoot_cases label contracted with ⟨name, rfl, rfl, value⟩ | plain
  · rw [value]
    simp only [List.map_cons, List.map_nil]
    rw [structural, contract_apply_of_ne (by decide)]
    simp [contractRoot]
  · rw [plain, structural, contract_apply, List.map_map]
    rfl

/-- **Lifting a contraction and contracting is lifting and contracting.** -/
theorem contract_liftBVars_contract (pattern : Pattern) :
    ∀ cutoff shift : Nat,
      contract (liftBVars cutoff shift (contract pattern)) =
        contract (liftBVars cutoff shift pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro cutoff shift; rw [contract]
  | hfvar name => intro cutoff shift; rw [contract]
  | happly label arguments ih =>
      intro cutoff shift
      have structural : ∀ (label : String) (arguments : List Pattern),
          liftBVars cutoff shift (.apply label arguments) =
            .apply label (arguments.map (liftBVars cutoff shift)) := by
        intro label arguments
        rw [liftBVars, liftBVarsList_eq_map]
      have right : contract (liftBVars cutoff shift (.apply label arguments)) =
          contractRoot label ((arguments.map contract).map fun part =>
            contract (liftBVars cutoff shift part)) := by
        rw [structural, contract_apply, List.map_map, List.map_map]
        congr 1
        exact List.map_congr_left fun argument member => (ih argument member cutoff shift).symm
      rw [right, contract_apply, contractRoot_map_change structural]
  | hlambda binder body ih =>
      intro cutoff shift
      simp only [contract, liftBVars]
      rw [ih]
  | hmultiLambda arity binders body ih =>
      intro cutoff shift
      simp only [contract, liftBVars]
      rw [ih]
  | hsubst body replacement ihBody ihReplacement =>
      intro cutoff shift
      simp only [contract, liftBVars]
      rw [ihBody, ihReplacement]
  | hcollection kind elements rest ih =>
      intro cutoff shift
      simp only [contract, liftBVars, contractList_eq_map, liftBVarsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => ih element member cutoff shift

/-- **Instantiating a contraction with a contraction and contracting is
instantiating and contracting.**  Contraction does not commute with the
instantiation of a binder: an argument that is a dropping, put beneath a
quotation, makes a quotation of a dropping that was not there. -/
theorem contract_instantiateBVarAt_contract (replacement : Pattern) (pattern : Pattern) :
    ∀ depth : Nat,
      contract (instantiateBVarAt depth (contract replacement) (contract pattern)) =
        contract (instantiateBVarAt depth replacement pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth
      rw [contract, instantiateBVarAt, instantiateBVarAt]
      split
      · rfl
      · split
        · exact contract_liftBVars_contract replacement 0 depth
        · rfl
  | hfvar name => intro depth; rw [contract, instantiateBVarAt, instantiateBVarAt]
  | happly label arguments ih =>
      intro depth
      have structural : ∀ (replacement : Pattern) (label : String) (arguments : List Pattern),
          instantiateBVarAt depth replacement (.apply label arguments) =
            .apply label (arguments.map (instantiateBVarAt depth replacement)) := by
        intro replacement label arguments
        rw [instantiateBVarAt]
      have right : contract (instantiateBVarAt depth replacement (.apply label arguments)) =
          contractRoot label ((arguments.map contract).map fun part =>
            contract (instantiateBVarAt depth (contract replacement) part)) := by
        rw [structural, contract_apply, List.map_map, List.map_map]
        congr 1
        exact List.map_congr_left fun argument member => (ih argument member depth).symm
      rw [right, contract_apply, contractRoot_map_change (structural (contract replacement))]
  | hlambda binder body ih =>
      intro depth
      simp only [contract, instantiateBVarAt]
      rw [ih]
  | hmultiLambda arity binders body ih =>
      intro depth
      simp only [contract, instantiateBVarAt]
      rw [ih]
  | hsubst body nested ihBody ihNested =>
      intro depth
      simp only [contract, instantiateBVarAt]
      rw [ihBody, ihNested]
  | hcollection kind elements rest ih =>
      intro depth
      simp only [contract, instantiateBVarAt, contractList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => ih element member depth

/-- **Negative**: contraction does not commute with the instantiation of a
binder.  The quotation of the bound variable, instantiated with a dropping,
is a quotation of a dropping. -/
theorem contract_instantiateBVar_ne :
    contract (instantiateBVar (dropped (quoted unitAtom)) (quoted (.bvar 0))) ≠
      instantiateBVar (contract (dropped (quoted unitAtom))) (contract (quoted (.bvar 0))) := by
  decide +kernel

/-! ## The instantiation of a binder changes no quotation of a sealed pattern -/

/-- The atom of a sealed quotation is closed. -/
theorem wellScoped_of_sealed_quotation {atom : Pattern} {scope : Nat}
    (safe : sealedAt scope (.apply "prime-quote" [atom]) = true) :
    atom.isWellScopedAt 0 = true := by
  have inner : sealedAt 0 atom = true := by simpa [sealedAt, binderSafeAt] using safe
  exact isWellScopedAt_of_binderSafeAt "prime-quote" inner

/-- **A sealed quotation is fixed by the instantiation of a binder**, at
every depth and for every argument: substitution does not enter it. -/
theorem instantiateBVarAt_quoted_of_sealed {atom : Pattern} {scope : Nat}
    (safe : sealedAt scope (quoted atom) = true) (depth : Nat) (replacement : Pattern) :
    instantiateBVarAt depth replacement (quoted atom) = quoted atom := by
  rw [quoted, instantiateBVarAt, List.map_cons, List.map_nil,
    instantiateBVarAt_eq_self_of_isWellScopedAt
      (isWellScopedAt_mono (wellScoped_of_sealed_quotation safe) (Nat.zero_le depth))]

mutual
  /-- **The quotations in a pattern**: its applications of the quotation
  constructor to one argument, those beneath a quotation included. -/
  def quotations : Pattern → List Pattern
    | .bvar _ => []
    | .fvar _ => []
    | .apply label arguments =>
        (if label = "prime-quote" ∧ arguments.length = 1 then [.apply label arguments] else []) ++
          quotationsList arguments
    | .lambda _ body => quotations body
    | .multiLambda _ _ body => quotations body
    | .subst body replacement => quotations body ++ quotations replacement
    | .collection _ elements _ => quotationsList elements

  /-- The quotations in the patterns of a list. -/
  def quotationsList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => quotations pattern ++ quotationsList patterns
end

/-- **Positive**: a quotation beneath a quotation is listed with the one
around it. -/
theorem quotations_nested :
    quotations (dropped (quoted (dropped (quoted unitAtom)))) =
      [quoted (dropped (quoted unitAtom)), quoted unitAtom] := by
  decide +kernel

/-- **Negative**: an atom of a term has no quotation. -/
theorem quotations_unitAtom : quotations (.apply "App" [unitAtom, unitAtom]) = [] := by
  decide +kernel

theorem mem_quotationsList {quotation : Pattern} :
    ∀ {patterns : List Pattern}, quotation ∈ quotationsList patterns ↔
      ∃ pattern ∈ patterns, quotation ∈ quotations pattern
  | [] => by simp [quotationsList]
  | pattern :: patterns => by
      rw [quotationsList, List.mem_append, mem_quotationsList (patterns := patterns)]
      simp

/-- The quotations of an application: itself, when it is a quotation, and
those of its arguments. -/
theorem mem_quotations_apply {quotation : Pattern} {label : String} {arguments : List Pattern} :
    quotation ∈ quotations (.apply label arguments) ↔
      (label = "prime-quote" ∧ arguments.length = 1 ∧ quotation = .apply label arguments) ∨
        ∃ argument ∈ arguments, quotation ∈ quotations argument := by
  rw [quotations, List.mem_append, mem_quotationsList]
  by_cases isQuotation : label = "prime-quote" ∧ arguments.length = 1
  · rw [if_pos isQuotation, List.mem_singleton]
    exact ⟨fun found => found.imp (fun same => ⟨isQuotation.1, isQuotation.2, same⟩) id,
      fun found => found.imp (fun both => both.2.2) id⟩
  · rw [if_neg isQuotation]
    exact ⟨fun found => found.elim (fun impossible => absurd impossible (List.not_mem_nil)) .inr,
      fun found => found.elim (fun both => absurd ⟨both.1, both.2.1⟩ isQuotation) .inr⟩

/-- **Every quotation of a lifted sealed pattern is a quotation of the
pattern.** -/
theorem mem_quotations_liftBVars (pattern : Pattern) :
    ∀ scope cutoff shift : Nat, sealedAt scope pattern = true →
      ∀ quotation ∈ quotations (liftBVars cutoff shift pattern),
        quotation ∈ quotations pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro scope cutoff shift _ quotation member
      rw [liftBVars] at member
      split at member <;> simp [quotations] at member
  | hfvar name =>
      intro scope cutoff shift _ quotation member
      rw [liftBVars] at member
      exact member
  | happly label arguments ih =>
      intro scope cutoff shift safe quotation member
      rw [liftBVars, liftBVarsList_eq_map] at member
      rcases mem_quotations_apply.mp member with ⟨isQuote, length, rfl⟩ | ⟨lifted, inLifted, inner⟩
      · subst isQuote
        rw [List.length_map] at length
        obtain ⟨atom, rfl⟩ := List.length_eq_one_iff.mp length
        rw [List.map_cons, List.map_nil, liftBVars_eq_self_of_isWellScopedAt
          (isWellScopedAt_mono (wellScoped_of_sealed_quotation safe) (Nat.zero_le cutoff))]
        exact mem_quotations_apply.mpr (.inl ⟨rfl, rfl, rfl⟩)
      · obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp inLifted
        exact mem_quotations_apply.mpr (.inr ⟨argument, inArguments,
          ih argument inArguments scope cutoff shift
            (sealedAt_of_mem_apply safe argument inArguments) quotation inner⟩)
  | hlambda binder body ih =>
      intro scope cutoff shift safe quotation member
      rw [sealedAt_lambda] at safe
      rw [liftBVars, quotations] at member
      rw [quotations]
      exact ih _ _ _ safe quotation member
  | hmultiLambda arity binders body ih =>
      intro scope cutoff shift safe quotation member
      have inner : sealedAt (scope + arity) body = true := by
        simpa [sealedAt, binderSafeAt] using safe
      rw [liftBVars, quotations] at member
      rw [quotations]
      exact ih _ _ _ inner quotation member
  | hsubst body replacement ihBody ihReplacement =>
      intro scope cutoff shift safe quotation member
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true] at safe
      rw [liftBVars, quotations, List.mem_append] at member
      rw [quotations, List.mem_append]
      exact member.imp (ihBody _ _ _ safe.1 quotation) (ihReplacement _ _ _ safe.2 quotation)
  | hcollection kind elements rest ih =>
      intro scope cutoff shift safe quotation member
      simp only [sealedAt, binderSafeAt] at safe
      rw [binderSafeListAt_eq_true_iff] at safe
      rw [liftBVars, liftBVarsList_eq_map, quotations, mem_quotationsList] at member
      rw [quotations, mem_quotationsList]
      obtain ⟨lifted, inLifted, inner⟩ := member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp inLifted
      exact ⟨element, inElements,
        ih element inElements scope cutoff shift (safe element inElements) quotation inner⟩

/-- **Every quotation of a sealed pattern is a quotation of its instance**:
the instantiation of a binder removes no quotation and changes none. -/
theorem quotations_subset_instantiateBVarAt (replacement : Pattern) (pattern : Pattern) :
    ∀ scope depth : Nat, sealedAt scope pattern = true →
      ∀ quotation ∈ quotations pattern,
        quotation ∈ quotations (instantiateBVarAt depth replacement pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro scope depth _ quotation member
      simp [quotations] at member
  | hfvar name =>
      intro scope depth _ quotation member
      simp [quotations] at member
  | happly label arguments ih =>
      intro scope depth safe quotation member
      rcases mem_quotations_apply.mp member with
        ⟨isQuote, length, rfl⟩ | ⟨argument, inArguments, inner⟩
      · subst isQuote
        obtain ⟨atom, rfl⟩ := List.length_eq_one_iff.mp length
        rw [show Pattern.apply "prime-quote" [atom] = quoted atom from rfl,
          instantiateBVarAt_quoted_of_sealed safe depth replacement]
        exact member
      · rw [instantiateBVarAt]
        exact mem_quotations_apply.mpr (.inr ⟨_, List.mem_map.mpr ⟨argument, inArguments, rfl⟩,
          ih argument inArguments scope depth (sealedAt_of_mem_apply safe argument inArguments)
            quotation inner⟩)
  | hlambda binder body ih =>
      intro scope depth safe quotation member
      rw [sealedAt_lambda] at safe
      rw [quotations] at member
      rw [instantiateBVarAt, quotations]
      exact ih _ _ safe quotation member
  | hmultiLambda arity binders body ih =>
      intro scope depth safe quotation member
      have inner : sealedAt (scope + arity) body = true := by
        simpa [sealedAt, binderSafeAt] using safe
      rw [quotations] at member
      rw [instantiateBVarAt, quotations]
      exact ih _ _ inner quotation member
  | hsubst body nested ihBody ihNested =>
      intro scope depth safe quotation member
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true] at safe
      rw [quotations, List.mem_append] at member
      rw [instantiateBVarAt, quotations, List.mem_append]
      exact member.imp (ihBody _ _ safe.1 quotation) (ihNested _ _ safe.2 quotation)
  | hcollection kind elements rest ih =>
      intro scope depth safe quotation member
      simp only [sealedAt, binderSafeAt] at safe
      rw [binderSafeListAt_eq_true_iff] at safe
      rw [quotations, mem_quotationsList] at member
      rw [instantiateBVarAt, quotations, mem_quotationsList]
      obtain ⟨element, inElements, inner⟩ := member
      exact ⟨_, List.mem_map.mpr ⟨element, inElements, rfl⟩,
        ih element inElements scope depth (safe element inElements) quotation inner⟩

/-- **Every quotation of an instance of a sealed pattern is a quotation of
the pattern or of the argument**, when the argument is sealed: the
instantiation of a binder makes no quotation. -/
theorem quotations_instantiateBVarAt_subset {replacement : Pattern} {ambient : Nat}
    (replacementSafe : sealedAt ambient replacement = true) (pattern : Pattern) :
    ∀ scope depth : Nat, sealedAt scope pattern = true →
      ∀ quotation ∈ quotations (instantiateBVarAt depth replacement pattern),
        quotation ∈ quotations pattern ∨ quotation ∈ quotations replacement := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro scope depth _ quotation member
      rw [instantiateBVarAt] at member
      split at member
      · simp [quotations] at member
      · split at member
        · exact .inr (mem_quotations_liftBVars replacement ambient 0 depth replacementSafe
            quotation member)
        · simp [quotations] at member
  | hfvar name =>
      intro scope depth _ quotation member
      rw [instantiateBVarAt] at member
      exact .inl member
  | happly label arguments ih =>
      intro scope depth safe quotation member
      rw [instantiateBVarAt] at member
      rcases mem_quotations_apply.mp member with
        ⟨isQuote, length, rfl⟩ | ⟨instantiated, inInstantiated, inner⟩
      · subst isQuote
        rw [List.length_map] at length
        obtain ⟨atom, rfl⟩ := List.length_eq_one_iff.mp length
        rw [List.map_cons, List.map_nil, instantiateBVarAt_eq_self_of_isWellScopedAt
          (isWellScopedAt_mono (wellScoped_of_sealed_quotation safe) (Nat.zero_le depth))]
        exact .inl (mem_quotations_apply.mpr (.inl ⟨rfl, rfl, rfl⟩))
      · obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp inInstantiated
        exact (ih argument inArguments scope depth
          (sealedAt_of_mem_apply safe argument inArguments) quotation inner).imp
          (fun found => mem_quotations_apply.mpr (.inr ⟨argument, inArguments, found⟩)) id
  | hlambda binder body ih =>
      intro scope depth safe quotation member
      rw [sealedAt_lambda] at safe
      rw [instantiateBVarAt, quotations] at member
      rw [quotations]
      exact ih _ _ safe quotation member
  | hmultiLambda arity binders body ih =>
      intro scope depth safe quotation member
      have inner : sealedAt (scope + arity) body = true := by
        simpa [sealedAt, binderSafeAt] using safe
      rw [instantiateBVarAt, quotations] at member
      rw [quotations]
      exact ih _ _ inner quotation member
  | hsubst body nested ihBody ihNested =>
      intro scope depth safe quotation member
      simp only [sealedAt, binderSafeAt, Bool.and_eq_true] at safe
      rw [instantiateBVarAt, quotations, List.mem_append] at member
      rw [quotations, List.mem_append]
      rcases member with inBody | inNested
      · exact (ihBody _ _ safe.1 quotation inBody).imp .inl id
      · exact (ihNested _ _ safe.2 quotation inNested).imp .inr id
  | hcollection kind elements rest ih =>
      intro scope depth safe quotation member
      simp only [sealedAt, binderSafeAt] at safe
      rw [binderSafeListAt_eq_true_iff] at safe
      rw [instantiateBVarAt, quotations, mem_quotationsList] at member
      rw [quotations, mem_quotationsList]
      obtain ⟨instantiated, inInstantiated, inner⟩ := member
      obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp inInstantiated
      exact (ih element inElements scope depth (safe element inElements) quotation inner).imp
        (fun found => ⟨element, inElements, found⟩) id

/-- **In a sealed pattern a beta step changes no quotation.**  For a sealed
redex `App(Lam(domain, body), argument)`: every quotation of the body is a
quotation of the contractum, and every quotation of the contractum is a
quotation of the body or of the argument. -/
theorem beta_keeps_quotations {depth : Nat} {domain body argument : Pattern}
    {binder : Option String}
    (safe : sealedAt depth
      (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument]) = true) :
    (∀ quotation ∈ quotations body, quotation ∈ quotations (instantiateBVar argument body)) ∧
      ∀ quotation ∈ quotations (instantiateBVar argument body),
        quotation ∈ quotations body ∨ quotation ∈ quotations argument := by
  have parts := (sealedAt_apply_of_ne (by decide) depth _).mp safe
  have argumentSafe : sealedAt depth argument = true := parts argument (by simp)
  have abstraction := (sealedAt_apply_of_ne (by decide) depth _).mp
    (parts (.apply "Lam" [domain, .lambda binder body]) (by simp))
  have bodySafe : sealedAt (depth + 1) body = true := by
    rw [← sealedAt_lambda depth binder body]
    exact abstraction (.lambda binder body) (by simp)
  exact ⟨quotations_subset_instantiateBVarAt argument body (depth + 1) 0 bodySafe,
    quotations_instantiateBVarAt_subset argumentSafe body (depth + 1) 0 bodySafe⟩

/-- **Negative**: the body that drops a quotation of the bound variable is
not sealed beneath its binder, and its quotation is not a quotation of its
instance: the instantiation went beneath it. -/
theorem quotation_changed_when_not_sealed :
    sealedAt 1 (dropped (quoted (.bvar 0))) = false ∧
      quoted (.bvar 0) ∈ quotations (dropped (quoted (.bvar 0))) ∧
        quoted (.bvar 0) ∉ quotations (instantiateBVar unitAtom (dropped (quoted (.bvar 0)))) := by
  decide +kernel

#print axioms sealedAt_quoted
#print axioms sealedAt_apply_of_ne
#print axioms sealedAt_of_mem_apply
#print axioms sealedAt_apply_map
#print axioms sealedAt_of_wellScoped
#print axioms plainSpace_ruleSpace
#print axioms not_plainSpace_quoting
#print axioms sealedAt_of_plainSpace
#print axioms runsPlain_apply
#print axioms runsPlain_runPattern
#print axioms runsPlain_of_tokens_eq_zero
#print axioms runsPlain_liftBVars
#print axioms runsPlain_instantiateBVarAt
#print axioms sealedWithPlainRuns_quotedRun
#print axioms not_sealedWithPlainRuns_capturing
#print axioms sealedWithPlainRuns_apply_iff
#print axioms sealedWithPlainRuns_runPattern
#print axioms contractRoot_cases
#print axioms sealedAt_contract
#print axioms contract_of_tokens_eq_zero
#print axioms runsPlain_contract
#print axioms SealedWithPlainRuns.contract
#print axioms contractRoot_map_change
#print axioms contract_liftBVars_contract
#print axioms contract_instantiateBVarAt_contract
#print axioms contract_instantiateBVar_ne
#print axioms instantiateBVarAt_quoted_of_sealed
#print axioms mem_quotations_apply
#print axioms mem_quotations_liftBVars
#print axioms quotations_subset_instantiateBVarAt
#print axioms quotations_instantiateBVarAt_subset
#print axioms beta_keeps_quotations
#print axioms quotation_changed_when_not_sealed

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
